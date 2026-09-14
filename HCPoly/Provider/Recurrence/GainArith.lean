/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.Moments

/-!
# The scalar estimates of the fixed-grid recurrence

Two displayed inequalities of `p.fixed.geometry.parent.child.recurrence` and of the
positive-gap estimate `l.fixed.geometry.positive.gap` are statements about real numbers
alone, and are proved here.

The first is the absorption step of `l.fixed.geometry.positive.gap`.  There the two
Schatten sizes `x` and `y`, the mean size `p` and the trace gap `b` satisfy
`x^Q ≤ C p^{Q-1} b + C y^{Q-1} x`, and Young's inequality turns this into the
linear bound `x ≤ C' (y + p^{1-1/Q} b^{1/Q})`.  The mechanism is a dichotomy:
either `x` is already comparable to `y`, or the term carrying `y` absorbs into
half of the left side and the remaining inequality is solved for `x` by taking
`Q`-th roots.  Both branches are recorded with their explicit witnesses, so the
constant is exhibited rather than merely asserted to exist.

The second is the terminal step of `p.fixed.geometry.parent.child.recurrence`.  The relative
mean of two consecutive scales has spectral size at most `e^Δ` and trace gap at
most `e^Δ - 1`, and the gain function
`Φ_Q(x) = e^{(1-1/Q)x}(e^x-1)^{1/Q} + (e^x - 1)` of the fixed-grid section is
exactly the value of `p^{1-1/Q} b^{1/Q} + b` at those two extremes.  Since both
factors are increasing in their bases, the bound is monotonicity of the real
power in the base, applied twice.
-/

namespace Homogenization
namespace HighContrast
namespace Recurrence

noncomputable section

/-! ## Exponents -/

/-- The conjugate exponent of an exponent at least one is nonnegative. -/
theorem one_sub_inv_nonneg {Q : ℝ} (hQ : 1 ≤ Q) : 0 ≤ 1 - Q⁻¹ := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hinv : Q⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hQ
  linarith only [hinv]

/-- The reciprocal of an exponent at least one is nonnegative. -/
theorem inv_nonneg_of_one_le {Q : ℝ} (hQ : 1 ≤ Q) : 0 ≤ Q⁻¹ :=
  inv_nonneg.mpr (le_trans zero_le_one hQ)

/-! ## The gain function -/

/-- The gain function `Φ_Q` of the fixed-grid section is nonnegative on the
nonnegative axis, where the determinant increment lives. -/
theorem gainPhi_nonneg {Q x : ℝ} (hx : 0 ≤ x) : 0 ≤ gainPhi Q x := by
  have hgap : (0 : ℝ) ≤ Real.exp x - 1 := by
    have := Real.one_le_exp hx
    linarith only [this]
  have h1 : (0 : ℝ) ≤ Real.exp ((1 - Q⁻¹) * x) := (Real.exp_pos _).le
  have h2 : (0 : ℝ) ≤ (Real.exp x - 1) ^ Q⁻¹ := Real.rpow_nonneg hgap _
  have : (0 : ℝ) ≤ Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹ := mul_nonneg h1 h2
  simpa only [gainPhi] using add_nonneg this hgap

/-- **The terminal estimate of `p.fixed.geometry.parent.child.recurrence`.**  A spectral size
bounded by `e^x` and a trace gap bounded by `e^x - 1` combine into the gain
`Φ_Q(x)`: the two printed extremes are attained simultaneously by the definition
of `Φ_Q`, and the real power is monotone in its base at a nonnegative
exponent. -/
theorem rpow_mul_rpow_add_le_gainPhi {Q x p b : ℝ} (hQ : 1 ≤ Q) (hx : 0 ≤ x)
    (hp : 0 ≤ p) (hpx : p ≤ Real.exp x) (hb : 0 ≤ b) (hbx : b ≤ Real.exp x - 1) :
    p ^ (1 - Q⁻¹) * b ^ Q⁻¹ + b ≤ gainPhi Q x := by
  have hgap : (0 : ℝ) ≤ Real.exp x - 1 := by
    have := Real.one_le_exp hx
    linarith only [this]
  have hfactor : p ^ (1 - Q⁻¹) ≤ Real.exp ((1 - Q⁻¹) * x) := by
    have hmono : p ^ (1 - Q⁻¹) ≤ Real.exp x ^ (1 - Q⁻¹) :=
      Real.rpow_le_rpow hp hpx (one_sub_inv_nonneg hQ)
    rwa [← Real.exp_mul, mul_comm x (1 - Q⁻¹)] at hmono
  have hgapfactor : b ^ Q⁻¹ ≤ (Real.exp x - 1) ^ Q⁻¹ :=
    Real.rpow_le_rpow hb hbx (inv_nonneg_of_one_le hQ)
  have hprod : p ^ (1 - Q⁻¹) * b ^ Q⁻¹ ≤
      Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹ :=
    mul_le_mul hfactor hgapfactor (Real.rpow_nonneg hb _) (Real.exp_pos _).le
  simpa only [gainPhi] using add_le_add hprod hbx

/-! ## The absorption step of the positive-gap estimate -/

/-- A nonnegative real is the `Q`-th power of its own `Q`-th root. -/
private theorem rpow_inv_rpow {Q t : ℝ} (hQ : 0 < Q) (ht : 0 ≤ t) : (t ^ Q) ^ Q⁻¹ = t := by
  rw [← Real.rpow_mul ht, mul_inv_cancel₀ (ne_of_gt hQ), Real.rpow_one]

/-- **The absorption step of `l.fixed.geometry.positive.gap`.**  Young's inequality applied
to `x^Q ≤ C p^{Q-1} b + C y^{Q-1} x` yields the linear bound with the explicit
constants `(2C)^{1/Q}` on the gap term and `(2C)^{1/(Q-1)}` on the fluctuation
term.

Either `x` is already at most `(2C)^{1/(Q-1)} y`, and the second summand alone
carries the bound, or it exceeds it; then `C y^{Q-1} x ≤ x^Q / 2`, half the left
side absorbs the fluctuation term, and taking `Q`-th roots in the remaining
inequality `x^Q ≤ 2C p^{Q-1} b` gives the first summand. -/
theorem le_rpow_add_of_rpow_le {Q C x y p b : ℝ} (hQ : 2 ≤ Q) (hC : 0 < C)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) (hb : 0 ≤ b)
    (h : x ^ Q ≤ C * p ^ (Q - 1) * b + C * y ^ (Q - 1) * x) :
    x ≤ (2 * C) ^ Q⁻¹ * (p ^ (1 - Q⁻¹) * b ^ Q⁻¹) + (2 * C) ^ (Q - 1)⁻¹ * y := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hQ1 : (1 : ℝ) ≤ Q - 1 := by linarith only [hQ]
  have hQ1pos : (0 : ℝ) < Q - 1 := lt_of_lt_of_le zero_lt_one hQ1
  have h2C : (0 : ℝ) < 2 * C := by linarith only [hC]
  set κ : ℝ := (2 * C) ^ (Q - 1)⁻¹ with hκdef
  have hκpos : (0 : ℝ) < κ := Real.rpow_pos_of_pos h2C _
  have hκpow : κ ^ (Q - 1) = 2 * C := by
    rw [hκdef, ← Real.rpow_mul h2C.le, inv_mul_cancel₀ (ne_of_gt hQ1pos), Real.rpow_one]
  -- The first summand is nonnegative, so the dichotomy may discard it.
  have hgapterm : (0 : ℝ) ≤ (2 * C) ^ Q⁻¹ * (p ^ (1 - Q⁻¹) * b ^ Q⁻¹) :=
    mul_nonneg (Real.rpow_nonneg h2C.le _)
      (mul_nonneg (Real.rpow_nonneg hp _) (Real.rpow_nonneg hb _))
  by_cases hcase : x ≤ κ * y
  · have : κ * y ≤ (2 * C) ^ Q⁻¹ * (p ^ (1 - Q⁻¹) * b ^ Q⁻¹) + κ * y := by
      linarith only [hgapterm]
    exact le_trans hcase this
  · push Not at hcase
    have hxpos : (0 : ℝ) < x := lt_of_le_of_lt (mul_nonneg hκpos.le hy) hcase
    -- The fluctuation term absorbs into half of the left side.
    have hyx : y ≤ x / κ := by
      rw [le_div_iff₀ hκpos]
      linarith only [hcase]
    have hypow : y ^ (Q - 1) ≤ x ^ (Q - 1) / (2 * C) := by
      have hmono : y ^ (Q - 1) ≤ (x / κ) ^ (Q - 1) :=
        Real.rpow_le_rpow hy hyx hQ1pos.le
      rwa [Real.div_rpow hx hκpos.le, hκpow] at hmono
    have hsplit : x ^ (Q - 1) * x = x ^ Q := by
      have hadd : x ^ (Q - 1 + 1) = x ^ (Q - 1) * x ^ (1 : ℝ) := Real.rpow_add hxpos _ _
      rw [Real.rpow_one] at hadd
      rw [← hadd]
      norm_num
    have habsorb : C * y ^ (Q - 1) * x ≤ x ^ Q / 2 := by
      have hstep : C * y ^ (Q - 1) ≤ C * (x ^ (Q - 1) / (2 * C)) :=
        mul_le_mul_of_nonneg_left hypow hC.le
      have hsimp : C * (x ^ (Q - 1) / (2 * C)) = x ^ (Q - 1) / 2 := by
        field_simp
      rw [hsimp] at hstep
      calc C * y ^ (Q - 1) * x ≤ x ^ (Q - 1) / 2 * x :=
            mul_le_mul_of_nonneg_right hstep hx
        _ = x ^ Q / 2 := by rw [← hsplit]; ring
    have hhalf : x ^ Q ≤ 2 * C * p ^ (Q - 1) * b := by
      have := h
      have hxQ : x ^ Q / 2 ≤ C * p ^ (Q - 1) * b := by linarith only [this, habsorb]
      linarith only [hxQ]
    -- Taking `Q`-th roots solves the remaining inequality for `x`.
    have hroot : x ≤ (2 * C * p ^ (Q - 1) * b) ^ Q⁻¹ := by
      have hmono : (x ^ Q) ^ Q⁻¹ ≤ (2 * C * p ^ (Q - 1) * b) ^ Q⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hx _) hhalf (inv_nonneg.mpr hQ0.le)
      rwa [rpow_inv_rpow hQ0 hx] at hmono
    have hfactor : (2 * C * p ^ (Q - 1) * b) ^ Q⁻¹ =
        (2 * C) ^ Q⁻¹ * (p ^ (1 - Q⁻¹) * b ^ Q⁻¹) := by
      have hexp : (Q - 1) * Q⁻¹ = 1 - Q⁻¹ := by
        field_simp
      rw [Real.mul_rpow (mul_nonneg h2C.le (Real.rpow_nonneg hp _)) hb,
        Real.mul_rpow h2C.le (Real.rpow_nonneg hp _), ← Real.rpow_mul hp, hexp, mul_assoc]
    rw [hfactor] at hroot
    have : (0 : ℝ) ≤ κ * y := mul_nonneg hκpos.le hy
    linarith only [hroot, this]

end

end Recurrence
end HighContrast
end Homogenization
