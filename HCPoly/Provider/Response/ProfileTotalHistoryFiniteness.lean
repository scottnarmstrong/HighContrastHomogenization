/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileSourceMaximum
import HCPoly.Provider.Response.ProfileMaximumLp
import HCPoly.Provider.Transport.CenteredTargetCells
import HCPoly.Provider.Transport.WindowCenteredSup

/-!
# Finiteness of the complete terminal history

The retained scales form a finite range.  At each scale, the common window
multiplier gives a finite `L^Q` bound for the centered response of the adapted
cell.  Summing those cell moments gives finiteness of the centered history; the
below-start source estimate and Minkowski then give finiteness of the complete
terminal history.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The retained centered history has finite mass under the common window
multiplier and the retained-cell enclosure. -/
theorem centeredHistory_ne_top_of_window [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Q rhoMax Cd : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {jStar M t : ℤ} {Y : CoeffSpace d → ℝ}
    (hCd : 1 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E)
    (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef)
    (hqeq : q = roundedGrid jStar m0) (hgrid : IsRoundedGrid jStar q)
    (hQ : 1 ≤ Q)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hcell : ∀ j : ℤ, jStar ≤ j → j ≤ t →
      adaptedCell q j ⊆ centeredCube d M)
    (hEt : BlockPosDef (adaptedMean P q t)) :
    centeredHistory P Q rhoMax q jStar t ≠ ⊤ := by
  subst q
  have hq : IsRoundedGrid jStar (roundedGrid jStar m0) := hgrid
  have hcenter := Transport.centeredHistory_le_sum_cell_moments (rhoMax := rhoMax)
    (lt_of_lt_of_le zero_lt_one hQ) hstat hq le_rfl hEt
  apply ne_top_of_le_ne_top ?_ hcenter
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  let X : CoeffSpace d → ℝ≥0∞ :=
    cellFamilyCenteredSup P Q {adaptedCell (roundedGrid jStar m0) j}
      (adaptedMean P (roundedGrid jStar m0) t)
  have hj' := Finset.mem_Icc.mp hj
  have hWmem : ∀ V ∈ ({adaptedCell (roundedGrid jStar m0) j} : Set (Set (Vec d))),
      ∃ y : Vec d,
        V = adaptedCellTranslate (roundedGrid jStar m0) j y := by
    intro V hV
    rw [Set.mem_singleton_iff] at hV
    subst V
    refine ⟨0, ?_⟩
    simp [adaptedCellTranslate]
  have hWcont : ∀ V ∈ ({adaptedCell (roundedGrid jStar m0) j} : Set (Set (Vec d))),
      V ⊆ centeredCube d M := by
    intro V hV
    rw [Set.mem_singleton_iff] at hV
    subst V
    exact hcell j hj'.1 hj'.2
  have hXLp := Transport.eLpNorm_cellFamilyCenteredSup_le
    (le_trans zero_le_one hCd) hg hE hY hm0 hq
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar m0) t)
    hEt hQ hj'.1 hWmem hWcont
  have hXLpTop : eLpNorm X (ENNReal.ofReal Q) P < ⊤ := by
    refine lt_of_le_of_lt hXLp ?_
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt (hY.lp_moment Q hQ) ENNReal.ofReal_lt_top
  have hXmoment : ∫⁻ a, X a ^ Q ∂P < ⊤ := by
    have hp0 : ENNReal.ofReal Q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
      (lt_of_lt_of_le zero_lt_one hQ)
    simpa only [enorm_eq_self,
      ENNReal.toReal_ofReal (le_trans zero_le_one hQ)] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 ENNReal.ofReal_ne_top hXLpTop
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun a ↦ ?_) hXmoment)
  apply ENNReal.rpow_le_rpow _ (le_trans zero_le_one hQ)
  have hmean : annealedBlock P (adaptedCell (roundedGrid jStar m0) j) =
      adaptedMean P (roundedGrid jStar m0) j := by
    rw [← PortableHistory.adaptedCellAt_zero]
    exact Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hstat hq hj'.1
      (Recurrence.hasMeasurableCoarseBlock_adaptedCell P
        (Recurrence.posDef_of_isRoundedGrid hq) j) 0
  refine le_trans (ENNReal.ofReal_le_ofReal (PortableHistory.blockSize_le_schattenSize
    (isSymmetricBlockMat_blockSub
      (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCell
        (roundedGrid jStar m0) j a)
      (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar m0) j))
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar m0) t) hEt
    (lt_of_lt_of_le zero_lt_one hQ))) ?_
  dsimp only [X, cellFamilyCenteredSup]
  refine le_iSup_of_le (adaptedCell (roundedGrid jStar m0) j)
    (le_iSup_of_le (Set.mem_singleton _) ?_)
  rw [hmean]

/-- The complete terminal history is finite using only the retained-window and
below-start source data. -/
theorem profileTotalHistory_ne_top_of_window [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Q rhoMax Cd : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {jStar M t : ℤ} {Y : CoeffSpace d → ℝ}
    (hCd : 1 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef)
    (hqeq : q = roundedGrid jStar m0) (hgrid : IsRoundedGrid jStar q)
    (hjt : jStar ≤ t) (hQ : 1 ≤ Q) (hrho : g < rhoMax)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hcell : ∀ j : ℤ, jStar ≤ j → j ≤ t →
      adaptedCell q j ⊆ centeredCube d M)
    (hbelow : ∀ k : ℤ, k < jStar → ∀ z ∈ containedCenters q k t,
      adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hYmean : ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y)
    (hYnorm : lqNorm P Q Y ≤ 2) :
    profileTotalHistory P Q rhoMax q jStar t (adaptedMean P q t) ≠ ⊤ := by
  have hcenter := centeredHistory_ne_top_of_window (rhoMax := rhoMax)
    hCd hg hE hY hm0 hqeq hgrid hQ hstat hcell hEt
  have hsourceBound := profileSourceMoment_le hCd hg hE hEpd hY hm0 hqeq hgrid
    hjt (hcell t hjt le_rfl) hbelow hrho hYmean hYnorm
  have hsource : profileSourceMoment P Q rhoMax q jStar t
      (adaptedMean P q t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsourceBound
  have hrootBound := profileTotalHistory_rpow_inv_le (rhoMax := rhoMax) hQ
    (Recurrence.posDef_of_isRoundedGrid hgrid) hjt hEt
    (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt
  have hroot : profileTotalHistory P Q rhoMax q jStar t
      (adaptedMean P q t) ^ Q⁻¹ ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.rpow_ne_top_of_nonneg (y := Q⁻¹) (by positivity) hcenter,
          hsource⟩)
    exact hrootBound
  intro htop
  apply hroot
  rw [htop, ENNReal.top_rpow_of_pos]
  positivity

end

end Homogenization.HighContrast.Response
