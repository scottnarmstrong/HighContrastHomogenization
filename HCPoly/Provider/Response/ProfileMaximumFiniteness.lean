/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileWeakFullLp
import HCPoly.Provider.Response.ProfileMaximumSkewLp
import HCPoly.Provider.Response.ProfileSourceMaximum

/-!
# Finiteness of the terminal response maximum

The retained part of the maximum ranges over finitely many scales and finitely
many aligned cells.  The below-start part is finite almost everywhere by the
single window multiplier.  Together these facts discharge the finiteness input
of the annealed-centered weak estimates without adding a source hypothesis.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The retained centered maximum is finite pointwise because both its scale
range and every aligned cell family are finite. -/
theorem profileCenteredMaximum_ne_top [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (a : CoeffSpace d) :
    profileCenteredMaximum P rhoMax q jStar t a ≠ ⊤ := by
  let C : ℝ≥0∞ :=
    ∑ k ∈ Finset.Icc jStar t,
      ∑ w ∈ alignedIndex q k t,
        ENNReal.ofReal
          ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
            blockSize
              (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
              (adaptedMean P q t))
  have hC : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.sum_ne_top.mpr fun k _ ↦
      ENNReal.sum_ne_top.mpr fun w _ ↦ ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top hC
  rw [profileCenteredMaximum_eq]
  refine iSup_le fun k ↦ iSup_le fun hjk ↦ iSup_le fun hkt ↦
    iSup_le fun w ↦ iSup_le fun hw ↦ ?_
  have hk : k ∈ Finset.Icc jStar t := Finset.mem_Icc.mpr ⟨hjk, hkt⟩
  have hw' : w ∈ alignedIndex q k t :=
    (mem_alignedIndex_iff hq hkt).mpr hw
  calc
    ENNReal.ofReal
          ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
            blockSize
              (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
              (adaptedMean P q t)) ≤
        ∑ v ∈ alignedIndex q k t,
          ENNReal.ofReal
            ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
              blockSize
                (blockSub (adaptedResponse q k v a) (adaptedMean P q k))
                (adaptedMean P q t)) := by
      exact Finset.single_le_sum
        (fun v _ ↦ (zero_le _ : (0 : ℝ≥0∞) ≤ _)) hw'
    _ ≤ C := by
      exact Finset.single_le_sum
        (fun r _ ↦ (zero_le _ : (0 : ℝ≥0∞) ≤ _)) hk

/-- The hatted all-scale maximum used by the weak estimates is finite almost
everywhere under the source/window and terminal-geometry data. -/
theorem ae_diagonalWeakMaximum_subSkew_ne_top [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Q rhoMax rhoDr rhoWn Cd : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {jStar M t : ℤ}
    {Y : CoeffSpace d → ℝ}
    (hCd : 1 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef)
    (hqeq : q = roundedGrid jStar m0) (hgrid : IsRoundedGrid jStar q)
    (hjt : jStar ≤ t)
    (hcell : adaptedCell q t ⊆ centeredCube d M)
    (hbelow : ∀ k : ℤ, k < jStar → ∀ z ∈ containedCenters q k t,
      adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hQ : 0 < Q) (hrhoSource : g < rhoMax)
    (hYmean : ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y)
    (hYnorm : lqNorm P Q Y ≤ 2)
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)))
    (h0 : Mat d) (hh0 : IsSkewMat h0) :
    ∀ᵐ a ∂P,
      diagonalWeakMaximum rhoWn q t
          (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0) ≠ ⊤ := by
  have hsourceBound := profileSourceMoment_le hCd hg hE hEpd hY hm0 hqeq
    hgrid hjt hcell hbelow hrhoSource hYmean hYnorm
  have hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hFsymm : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hsourceMeas : AEMeasurable
      (profileSourceMaximum rhoMax q jStar t (adaptedMean P q t)) P :=
    aemeasurable_profileSourceMaximum hq hjt hFsymm hEt
  have hsourceFinite : ∀ᵐ a ∂P,
      profileSourceMaximum rhoMax q jStar t (adaptedMean P q t) a ≠ ⊤ := by
    apply ae_ne_top_of_eLpNorm_le_ofReal hQ hsourceMeas
    exact hsourceBound
  filter_upwards [hsourceFinite] with a hsource
  have hcenter : profileCenteredMaximum P rhoMax q jStar t a ≠ ⊤ :=
    profileCenteredMaximum_ne_top hq a
  have htotal :
      profileTotalMaximum P rhoMax q jStar t (adaptedMean P q t) a ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hcenter, hsource⟩
  have hpoint := diagonalWeakMaximum_subSkew_le_profileTotalMaximum_add_drift
    hrhoMax hrhoDr hrhoDrWn hq hEt hmono h0 hh0 a
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨htotal, ENNReal.ofReal_ne_top⟩) hpoint

end

end Homogenization.HighContrast.Response
