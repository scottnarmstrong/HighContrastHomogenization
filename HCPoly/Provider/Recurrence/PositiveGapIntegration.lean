/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.PositiveGap
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The positive-gap estimate in the mixed norm

The trace-power display of `l.fixed.geometry.positive.gap` is pointwise; the estimate the
lemma states is between mixed norms.  The passage between the two is the step
the reference proof records as "using `tr D ≤ m^{1-1/Q}|D|_{S_Q}` and applying
Hölder's inequality", and it is taken here.

The pointwise inequality has two summands.  The first is a multiple of the
trace, whose mean is the gap `b`, so integrating it is the definition of `b` and
nothing more.  The second is a multiple of `|Y|_{S_Q}^{Q-1}|D|_{S_Q}`, a product
of a function in `L^{Q/(Q-1)}` with one in `L^Q`; Hölder's inequality at that
conjugate pair turns its mean into `y^{Q-1}x`.  Raising the `L^Q` norm to the
power `Q` is what puts the left side in `L^1` alongside them, and the resulting
inequality `x^Q ≤ Cp^{Q-1}b + Cy^{Q-1}x` is the quadratic display the absorption
step consumes.

Everything is written in `ℝ≥0∞`, as the mixed norms of the fixed-grid section
are: no finiteness is assumed of `x` or `y`, and the gap enters through the
bound `E[tr D] ≤ b` rather than through an equality, which is the form the
recurrence has it in.
-/

namespace Homogenization
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The conjugate pair -/

/-- The exponents `Q/(Q-1)` and `Q` are Hölder conjugate: this is the pair the
positive-gap estimate pairs the fluctuation against the excess in. -/
private theorem holderTriple_div_sub_one {Q : ℝ} (hQ : 2 ≤ Q) :
    ENNReal.HolderTriple (ENNReal.ofReal (Q / (Q - 1))) (ENNReal.ofReal Q) 1 := by
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQ]
  have hQ1 : (0 : ℝ) < Q - 1 := by linarith only [hQ]
  have hpos : (0 : ℝ) < Q / (Q - 1) := div_pos hQ0 hQ1
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_inv_of_pos hQ0,
    ← ENNReal.ofReal_add (by positivity) (by positivity), inv_one,
    show (Q / (Q - 1))⁻¹ + Q⁻¹ = 1 by field_simp; ring]
  simp

/-! ## The integrated trace-power display -/

/-- **The quadratic display of `l.fixed.geometry.positive.gap`.**  A pointwise bound
`u^Q ≤ α t + β v^{Q-1} u` on nonnegative measurable data integrates to
`x^Q ≤ α b + β y^{Q-1} x` for the `L^Q` norms `x` of `u` and `y` of `v` and any
bound `b` on the mean of `t`.  The left side becomes an `L^1` norm when raised
to the power `Q`; the first summand is the mean of `t`; and the second is
Hölder's inequality at the conjugate pair `Q/(Q-1)`, `Q`. -/
theorem eLpNorm_rpow_le_add_mul (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 2 ≤ Q)
    {u v t : CoeffSpace d → ℝ} {α β b : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) (hmu : AEStronglyMeasurable u P)
    (hmv : AEStronglyMeasurable v P) (hmt : AEStronglyMeasurable t P)
    (hpt : ∀ a, u a ^ Q ≤ α * t a + β * (v a ^ (Q - 1) * u a))
    (hgap : eLpNorm t 1 P ≤ ENNReal.ofReal b) :
    eLpNorm u (ENNReal.ofReal Q) P ^ Q ≤
      ENNReal.ofReal (α * b) +
        ENNReal.ofReal β *
          (eLpNorm v (ENNReal.ofReal Q) P ^ (Q - 1) * eLpNorm u (ENNReal.ofReal Q) P) := by
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQ]
  have hQ1 : (0 : ℝ) < Q - 1 := by linarith only [hQ]
  have hne : Q - 1 ≠ 0 := ne_of_gt hQ1
  have hmw : AEStronglyMeasurable (fun a => v a ^ (Q - 1)) P :=
    (Real.continuous_rpow_const hQ1.le).comp_aestronglyMeasurable hmv
  -- The `Q`-th power of the `L^Q` norm is an `L^1` norm.
  have hpow : eLpNorm u (ENNReal.ofReal Q) P ^ Q = eLpNorm (fun a => u a ^ Q) 1 P := by
    have hfun : (fun a => u a ^ Q) = fun a => ‖u a‖ ^ Q := by
      funext a
      rw [Real.norm_of_nonneg (hu a)]
    rw [hfun, eLpNorm_norm_rpow u hQ0, one_mul]
  -- The pointwise bound, read in `L^1`.
  have hmono : eLpNorm (fun a => u a ^ Q) 1 P ≤
      eLpNorm ((fun a => α * t a) + fun a => β * (v a ^ (Q - 1) * u a)) 1 P := by
    refine eLpNorm_mono_real fun a => ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hu a) Q)]
    exact hpt a
  have hsub := eLpNorm_add_le (μ := P) (p := 1) (f := fun a => α * t a)
    (g := fun a => β * (v a ^ (Q - 1) * u a)) (hmt.const_mul α)
    ((hmw.mul hmu).const_mul β) le_rfl
  -- The two summands.
  have hfirst : eLpNorm (fun a => α * t a) 1 P = ENNReal.ofReal α * eLpNorm t 1 P := by
    have hfun : (fun a => α * t a) = α • t := by
      funext a
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hα]
  have hsecond : eLpNorm (fun a => β * (v a ^ (Q - 1) * u a)) 1 P =
      ENNReal.ofReal β * eLpNorm (fun a => v a ^ (Q - 1) * u a) 1 P := by
    have hfun : (fun a => β * (v a ^ (Q - 1) * u a)) = β • fun a => v a ^ (Q - 1) * u a := by
      funext a
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hβ]
  -- Hölder's inequality at the conjugate pair.
  haveI := holderTriple_div_sub_one hQ
  have hholder : eLpNorm (fun a => v a ^ (Q - 1) * u a) 1 P ≤
      eLpNorm (fun a => v a ^ (Q - 1)) (ENNReal.ofReal (Q / (Q - 1))) P *
        eLpNorm u (ENNReal.ofReal Q) P := by
    have hfun : (fun a => v a ^ (Q - 1) * u a) = (fun a => v a ^ (Q - 1)) • u := rfl
    rw [hfun]
    exact eLpNorm_smul_le_mul_eLpNorm hmu hmw
  -- The fluctuation norm at the conjugate exponent is the `L^Q` norm powered.
  have hconj : eLpNorm (fun a => v a ^ (Q - 1)) (ENNReal.ofReal (Q / (Q - 1))) P =
      eLpNorm v (ENNReal.ofReal Q) P ^ (Q - 1) := by
    have hfun : (fun a => v a ^ (Q - 1)) = fun a => ‖v a‖ ^ (Q - 1) := by
      funext a
      rw [Real.norm_of_nonneg (hv a)]
    have hexp : ENNReal.ofReal (Q / (Q - 1)) * ENNReal.ofReal (Q - 1) = ENNReal.ofReal Q := by
      rw [← ENNReal.ofReal_mul (div_pos hQ0 hQ1).le]
      congr 1
      field_simp
    rw [hfun, eLpNorm_norm_rpow v hQ1, hexp]
  rw [hpow]
  refine le_trans hmono (le_trans hsub ?_)
  rw [hfirst, hsecond, ENNReal.ofReal_mul hα]
  refine add_le_add (mul_le_mul_right hgap _) (mul_le_mul_right ?_ _)
  rw [← hconj]
  exact hholder

/-! ## The display in the Schatten carriers -/

/-- **The quadratic display of `l.fixed.geometry.positive.gap` in the carriers of the
fixed-grid section.**  The excess `D` of the averaged response over the response
is positive and dominated by `Ĝ = P + Y`; its mixed norm then satisfies
`x^Q ≤ C|P|^{Q-1}b + Cy^{Q-1}x` with the constants of the trace-power display,
`b` being any bound on the mean of `tr D`.  This is the inequality the
absorption step of the estimate is applied to. -/
theorem eLpNorm_schattenNorm_rpow_le (P : Measure (CoeffSpace d)) (hd : 0 < d) {Q : ℝ}
    (hQ : 2 ≤ Q) {D Gh Pm Y : CoeffSpace d → BlockMat d} {p b : ℝ} (hp : 0 ≤ p)
    (hD : ∀ a, IsSymmetricBlockMat (D a)) (hDpos : ∀ a, (toFullBlockMat (D a)).PosSemidef)
    (hY : ∀ a, IsSymmetricBlockMat (Y a))
    (hsplit : ∀ a, toFullBlockMat (Gh a) = toFullBlockMat (Pm a) + toFullBlockMat (Y a))
    (hPm : ∀ a, toFullBlockMat (Pm a) ≤ p • (1 : FullBlockMat d))
    (hDG : ∀ a, toFullBlockMat (D a) ≤ toFullBlockMat (Gh a))
    (hmD : AEStronglyMeasurable (fun a => schattenNorm Q (D a)) P)
    (hmY : AEStronglyMeasurable (fun a => schattenNorm Q (Y a)) P)
    (hmT : AEStronglyMeasurable (fun a => blockTrace (D a)) P)
    (hgap : eLpNorm (fun a => blockTrace (D a)) 1 P ≤ ENNReal.ofReal b) :
    eLpNorm (fun a => schattenNorm Q (D a)) (ENNReal.ofReal Q) P ^ Q ≤
      ENNReal.ofReal ((2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) * b) +
        ENNReal.ofReal ((2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹)) *
          (eLpNorm (fun a => schattenNorm Q (Y a)) (ENNReal.ofReal Q) P ^ (Q - 1) *
            eLpNorm (fun a => schattenNorm Q (D a)) (ENNReal.ofReal Q) P) := by
  have hα : (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hp _)
  have hβ : (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _)
  exact eLpNorm_rpow_le_add_mul P hQ hα hβ (fun a => zero_le_schattenNorm (hD a) Q)
    (fun a => zero_le_schattenNorm (hY a) Q) hmD hmY hmT
    (fun a => schattenNorm_rpow_le_add_mul_schattenNorm hd (hD a) (hDpos a) (hY a) hQ hp
      (hsplit a) (hPm a) (hDG a))
    hgap

end

end Recurrence
end HighContrast
end Homogenization
