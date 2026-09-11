/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentCellLp
import HCPoly.Provider.Response.ProfileRecentAverageSum
import HCPoly.Provider.Response.ConstantSkewProfiles

/-!
# Recent profile bounds after skew recentering

The recent cell and averaged-defect sums are invariant when the coefficient
sample and terminal mean are transformed by the same constant shear.  Their
probabilistic bounds therefore retain the portable, unhatted histories.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The recent-cell `L²` estimate in the constant-skew coordinates. -/
theorem eLpNorm_diagonalWeakCellSum_subSkew_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} {H : ℕ}
    {Q alpha rhoMax : ℝ} (hQ : 2 ≤ Q) (hrho : 0 ≤ rhoMax)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ))
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) :
    eLpNorm
        (fun coeff ↦ diagonalWeakCellSum q t H (1 / 2)
          (skewBlockCongr g (adaptedMean P q t)) (coeff.subSkew g hg)) 2 P ≤
      ENNReal.ofReal (centeredWindowCoefficient H rhoMax) *
          centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ +
        ENNReal.ofReal (nonlinearCellWindowCoefficient H alpha Q) *
          nonlinearHistory P Q alpha q jStar t ^ Q⁻¹ := by
  have hfun :
      (fun coeff ↦ diagonalWeakCellSum q t H (1 / 2)
        (skewBlockCongr g (adaptedMean P q t)) (coeff.subSkew g hg)) =
        fun coeff ↦ diagonalWeakCellSum q t H (1 / 2)
          (adaptedMean P q t) coeff := by
    funext coeff
    exact diagonalWeakCellSum_subSkew hq t H (1 / 2)
      (adaptedMean P q t) coeff g hg
  rw [hfun]
  exact eLpNorm_diagonalWeakCellSum_le_profile hq hQ hrho hP hgrid hlj
    hfin hstart hEt hmean

/-- The recent averaged-defect `L²` estimate in the constant-skew
coordinates. -/
theorem eLpNorm_diagonalWeakAverageSum_subSkew_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} {H : ℕ}
    {Q alpha s rho : ℝ} (hQ : 1 ≤ Q) (hexponent : s - rho / 2 = alpha)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ))
    (g : Mat d) (hg : IsSkewMat g) :
    eLpNorm
        (fun coeff ↦ diagonalWeakAverageSum q t H s rho
          (skewBlockCongr g (adaptedMean P q t)) (coeff.subSkew g hg)) 2 P ≤
      ENNReal.ofReal (nonlinearAverageWindowCoefficient H alpha Q) *
        nonlinearHistory P Q alpha q jStar t ^ (1 / (2 * Q)) := by
  have hjt : jStar ≤ t :=
    hstart.trans (sub_le_self t (Int.natCast_nonneg H))
  have hint : HasFiniteAdaptedMean P q t := hfin t hjt le_rfl
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t hint
  have hEsymm : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hfun :
      (fun coeff ↦ diagonalWeakAverageSum q t H s rho
        (skewBlockCongr g (adaptedMean P q t)) (coeff.subSkew g hg)) =
        fun coeff ↦ diagonalWeakAverageSum q t H s rho
          (adaptedMean P q t) coeff := by
    funext coeff
    exact diagonalWeakAverageSum_subSkew hq t H s rho hEsymm hEt coeff g hg
  rw [hfun]
  exact eLpNorm_diagonalWeakAverageSum_le_profile hq hQ hexponent hP hgrid
    hlj hfin hstart

end

end Homogenization.HighContrast.Response
