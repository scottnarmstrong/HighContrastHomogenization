/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.StrongTailLp
import HCPoly.Provider.Window.WindowMultiplierStrongTail
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The stopped window multiplier satisfies the source moment display at every
real exponent at least one. -/
theorem windowMultiplier_lp_moment [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {jStar M : ℤ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M) :
    ∀ p : ℝ, 1 ≤ p →
      eLpNorm (windowMultiplier g E jStar M) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal
          (1 + sourceRemainderScale d jStar K *
            momentMultiplier p (growthBar K)) := by
  intro p hp
  let A : ℝ := sourceRemainderScale d jStar K
  let W : CoeffSpace d → ℝ := fun a =>
    (windowMultiplier g E jStar M a - 1) / A
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hB : 2 ≤ growthBar K := by
    rw [growthBar]
    exact le_max_left _ _
  have hA : 0 < A := by
    dsimp only [A, sourceRemainderScale]
    exact mul_pos (pow_pos (lt_of_lt_of_le zero_lt_two hB) _)
      (zpow_pos (by norm_num) _)
  have hYm : Measurable (windowMultiplier g E jStar M) :=
    measurable_windowMultiplier g E hdag.refBlock_isSymm hdag.refBlock_posDef jStar M
  have hWm : AEMeasurable W P := by
    exact ((hYm.sub measurable_const).div_const A).aemeasurable
  have hW0 : ∀ a, 0 ≤ W a := by
    intro a
    dsimp only [W]
    exact div_nonneg
      (sub_nonneg.mpr (one_le_windowMultiplier hg.1 E jStar M a)) hA.le
  have htail : ∀ ⦃t : ℝ⦄, 1 ≤ t →
      P.real {a : CoeffSpace d | t < W a} ≤ (t * Ψ t)⁻¹ := by
    intro t ht
    simpa only [W, A] using
      normalized_windowMultiplier_sub_one_strong_tail hstat hdag hg hQ hw ht
  have hgrowth : IndependentSums.HasPsiGrowth Ψ (growthBar K) :=
    hasPsiGrowth_mono hdag.gauge_admissible
      (le_of_lt hdag.one_lt_growthWitness) (le_max_right _ _) hdag.gauge_growth
  have hWnorm : eLpNorm W (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (momentMultiplier p (growthBar K)) := by
    simpa only [momentMultiplier, one_div] using
      IndependentSums.eLpNorm_le_of_strongPsiTail
        hB hgrowth hdag.gauge_admissible hWm hW0 htail hp
  have hM0 : 0 ≤ momentMultiplier p (growthBar K) := by
    rw [momentMultiplier]
    apply Real.rpow_nonneg
    have hlog : 0 ≤ Real.log (growthBar K) :=
      Real.log_nonneg (one_le_two.trans hB)
    have hzpow : 0 < growthBar K ^ (⌈p * (p + 1) / 2⌉ : ℤ) :=
      zpow_pos (lt_of_lt_of_le zero_lt_two hB) _
    positivity
  have hfun : windowMultiplier g E jStar M =
      (fun _ : CoeffSpace d => (1 : ℝ)) + fun a => A * W a := by
    funext a
    dsimp only [Pi.add_apply, W]
    field_simp [hA.ne']
    ring
  have hpenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hadd := eLpNorm_add_le (p := ENNReal.ofReal p) (μ := P)
    (f := fun _ : CoeffSpace d => (1 : ℝ)) (g := fun a => A * W a)
    aestronglyMeasurable_const (hWm.aestronglyMeasurable.const_mul A) hpenn
  have hconst : eLpNorm (fun _ : CoeffSpace d => (1 : ℝ))
      (ENNReal.ofReal p) P = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hp0).ne'
      (IsProbabilityMeasure.ne_zero P), measure_univ, ENNReal.one_rpow, mul_one]
    norm_num
  have hsmul : eLpNorm (fun a => A * W a) (ENNReal.ofReal p) P =
      ENNReal.ofReal A * eLpNorm W (ENNReal.ofReal p) P := by
    rw [show (fun a => A * W a) = A • W from rfl, eLpNorm_const_smul,
      Real.enorm_eq_ofReal hA.le]
  rw [hfun]
  calc
    eLpNorm ((fun _ : CoeffSpace d => (1 : ℝ)) + fun a => A * W a)
        (ENNReal.ofReal p) P ≤
        eLpNorm (fun _ : CoeffSpace d => (1 : ℝ)) (ENNReal.ofReal p) P +
          eLpNorm (fun a => A * W a) (ENNReal.ofReal p) P := hadd
    _ = 1 + ENNReal.ofReal A * eLpNorm W (ENNReal.ofReal p) P := by
      rw [hconst, hsmul]
    _ ≤ 1 + ENNReal.ofReal A *
        ENNReal.ofReal (momentMultiplier p (growthBar K)) := by gcongr
    _ = ENNReal.ofReal
        (1 + sourceRemainderScale d jStar K *
          momentMultiplier p (growthBar K)) := by
      rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hA.le hM0),
        ENNReal.ofReal_one, ENNReal.ofReal_mul hA.le]

end
end Window
end HighContrast
end Homogenization

