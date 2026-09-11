/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileTotalHistoryFiniteness
import HCPoly.Provider.Response.ProfileEnergySkew
import HCPoly.Provider.Response.ProfileMaximumSkewLp
import HCPoly.Provider.Bridge.LinearDrift

/-!
# Optimizer-energy bounds from window data

The finite complete history supplied by the window estimates is converted to
its exact real value.  This discharges the complete-maximum hypotheses in the
bad-event estimates, while the good-event estimates remain pointwise.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The four primal/adjoint bad/good optimizer-energy estimates follow from
the retained window and source data, with no separate history-finiteness
assumption. -/
theorem profileEnergy_subSkew_le_of_window [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Q rhoMax rhoDr rhoWn Cd alpha : ℝ} {H : ℕ}
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {jStar M t : ℤ} {Y : CoeffSpace d → ℝ}
    (hCd : 1 ≤ Cd) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef)
    (hqeq : q = roundedGrid jStar m0) (hgrid : IsRoundedGrid jStar q)
    (hjt : jStar ≤ t) (hQ : 2 < Q) (hrho : g < rhoMax)
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hcell : ∀ j : ℤ, jStar ≤ j → j ≤ t →
      adaptedCell q j ⊆ centeredCube d M)
    (hbelow : ∀ k : ℤ, k < jStar → ∀ z ∈ containedCenters q k t,
      adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ t →
      HasFiniteAdaptedMean P q j ∧ BlockPosDef (adaptedMean P q j))
    (hYmean : ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y)
    (hYnorm : lqNorm P Q Y ≤ 2)
    (s : Mat d) (hs : IsSkewMat s) (p r : Vec d) :
    let hTot :=
      (profileTotalHistory P Q rhoMax q jStar t (adaptedMean P q t)).toReal
    let beta := linearDrift P rhoDr q jStar t
    profileBadEnergy P
        (fun a ↦ diagonalWeakMaximum rhoWn q t
          (skewBlockCongr s (adaptedMean P q t)) (a.subSkew s hs))
        (fun a ↦ diagonalWeakEnergy (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (a.subSkew s hs) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        profileEnergyLoad
          (diagonalWeakLoadMinus
            (skewBlockCongr s (adaptedMean P q t)) p r) p r *
        profileBadMajorant Q hTot beta) ∧
    profileBadEnergy P
        (fun a ↦ diagonalWeakMaximum rhoWn q t
          (skewBlockCongr s (adaptedMean P q t)) (a.subSkew s hs))
        (fun a ↦ diagonalWeakAdjointEnergy
          (Recurrence.posDef_of_isRoundedGrid hgrid) t (a.subSkew s hs) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        profileEnergyLoad
          (diagonalWeakLoadPlus
            (skewBlockCongr s (adaptedMean P q t)) p r) p r *
        profileBadMajorant Q hTot beta) ∧
    profileGoodEnergy P alpha H
        (fun a ↦ diagonalWeakMaximum rhoWn q t
          (skewBlockCongr s (adaptedMean P q t)) (a.subSkew s hs))
        (fun a ↦ diagonalWeakEnergy (Recurrence.posDef_of_isRoundedGrid hgrid) t
          (a.subSkew s hs) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 * (3 : ℝ) ^ (-alpha * (H : ℝ)) *
        profileEnergyLoad
          (diagonalWeakLoadMinus
            (skewBlockCongr s (adaptedMean P q t)) p r) p r) ∧
    profileGoodEnergy P alpha H
        (fun a ↦ diagonalWeakMaximum rhoWn q t
          (skewBlockCongr s (adaptedMean P q t)) (a.subSkew s hs))
        (fun a ↦ diagonalWeakAdjointEnergy
          (Recurrence.posDef_of_isRoundedGrid hgrid) t (a.subSkew s hs) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 * (3 : ℝ) ^ (-alpha * (H : ℝ)) *
        profileEnergyLoad
          (diagonalWeakLoadPlus
            (skewBlockCongr s (adaptedMean P q t)) p r) p r) := by
  dsimp only
  have hQone : 1 ≤ Q := le_trans (by norm_num) hQ.le
  have hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hEt : BlockPosDef (adaptedMean P q t) := (hfin t hjt le_rfl).2
  have hfinite := profileTotalHistory_ne_top_of_window hCd hg1 hE hEpd hY
    hm0 hqeq hgrid hjt hQone hrho hstat hcell hbelow
    hEt hYmean hYnorm
  let hTot :=
    (profileTotalHistory P Q rhoMax q jStar t (adaptedMean P q t)).toReal
  let beta := linearDrift P rhoDr q jStar t
  have hh : 0 ≤ hTot := ENNReal.toReal_nonneg
  have hbeta : 0 ≤ beta := by
    exact Bridge.linearDrift_nonneg hstat hgrid le_rfl hjt
      (fun j hj hlt ↦ (hfin j hj hlt).1) rhoDr
  have hmono : ∀ u : ℤ, jStar + 1 ≤ u → u ≤ t →
      BlockMatLoewnerLE (adaptedMean P q u) (adaptedMean P q (u - 1)) := by
    intro u hu hut
    exact Recurrence.adaptedMean_le hstat hgrid (by omega) (by omega)
      (hfin (u - 1) (by omega) (by omega)).1
      (hfin u (by omega) hut).1
  let W := profileTotalMaximum P rhoMax q jStar t (adaptedMean P q t)
  have hW : AEMeasurable W P :=
    aemeasurable_profileTotalMaximum hq hjt hEt
      (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt
  have hpoint : ∀ a, diagonalWeakMaximum rhoWn q t
      (adaptedMean P q t) a ≤ W a + ENNReal.ofReal beta := by
    exact diagonalWeakMaximum_le_profileTotalMaximum_add_drift
      hrhoMax hrhoDr hrhoDrWn hq hEt hmono
  have hnorm : eLpNorm (diagonalWeakMaximum rhoWn q t
      (adaptedMean P q t)) (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (hTot ^ Q⁻¹ + beta) := by
    calc
      _ ≤ profileTotalHistory P Q rhoMax q jStar t
            (adaptedMean P q t) ^ Q⁻¹ + ENNReal.ofReal beta :=
        eLpNorm_diagonalWeakMaximum_le_profile hQone hrhoMax hrhoDr
          hrhoDrWn hq hjt hEt hmono
      _ = ENNReal.ofReal (hTot ^ Q⁻¹ + beta) := by
        rw [← ENNReal.ofReal_toReal hfinite,
          ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
          ENNReal.ofReal_add (Real.rpow_nonneg hh _) hbeta]
  have hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal hTot := by
    rw [show (∫⁻ a, W a ^ Q ∂P) =
        profileTotalHistory P Q rhoMax q jStar t (adaptedMean P q t) by rfl,
      ENNReal.ofReal_toReal hfinite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact profileBadEnergy_subSkew_le hQ hh hbeta hq
      (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt hW hpoint hnorm
      hmoment s hs p r
  · exact profileBadAdjointEnergy_subSkew_le hQ hh hbeta hq
      (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt hW hpoint hnorm
      hmoment s hs p r
  · exact profileGoodEnergy_subSkew_le hq
      (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt s hs p r
  · exact profileGoodAdjointEnergy_subSkew_le hq
      (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt s hs p r

end

end Homogenization.HighContrast.Response
