/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.Moments

/-!
# The scalar kernels of the grid transport

The transport of a complete history across one change of adapted geometry
carries each source scale to each target scale through a scalar coefficient.
This file proves the arithmetic of those coefficients.  Everything here is a
statement about real numbers: the dimension, the two growth exponents, the
moment exponent and the scale differences enter only as reals, and no matrix,
measure or cell appears.

Three exponent relations drive the whole calculation.  The defining relation of
the derived exponent, `a = Q(ρ_max - g) - d`, says exactly that the target
multiplicity `3^{d/Q}` per unit of scale converts the maximal weight
`3^{-ρ_max}` into `3^{-(g + a/Q)}`; this is the cost of replacing the maximum
over target cells by a sum.  Its `Q`-th power form,
`Qρ_max - d = Qg + a`, is what makes the target coefficient of the centered
history summable against the nonlinear row weight.  The two admissibility
conditions of the subsection give the two signs the kernels need: the boundary
exponent `(d+1)/2 - a/Q` is positive, so the boundary kernel is summable, and
the bulk exponent `a/Q - d/2` is negative, so the adaptive bulk kernel loses
nothing beyond the buffer factor.

The boundary kernel is an identity rather than an estimate.  Once the terminal
scales are related by `t = n + ℓ₀`, the product of the target multiplicity and
the boundary square weight is *exactly* the printed coefficient built from the
normalized moment `u_r = 3^{-a(t-r)/Q}e^{Δ_{r,t}}v_r`, with the buffer factor
`3^{aℓ₀/Q}` and no slack.  The bulk kernel is a genuine inequality, and the
only place where the sign of `a/Q - d/2` is used.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

/-! ## The exponent relations -/

/-- The defining relation of the derived exponent, read at the level of the
`Q`-th root: the maximal weight discounted by the target multiplicity is the
weight of exponent `g + a/Q`. -/
theorem root_exponent_eq {d g Q rhoMax a : ℝ} (hQ : 0 < Q)
    (hadef : a = Q * (rhoMax - g) - d) :
    rhoMax - d / Q = g + a / Q := by
  subst hadef
  field_simp
  ring

/-- The defining relation of the derived exponent, read at the level of the
`Q`-th power. -/
theorem power_exponent_eq {d g Q rhoMax a : ℝ}
    (hadef : a = Q * (rhoMax - g) - d) :
    Q * rhoMax - d = Q * g + a := by
  subst hadef
  ring

/-- The `Q`-th power target exponent is positive: it is `Qg + a` with `a`
positive and `g` nonnegative. -/
theorem power_exponent_pos {d g Q rhoMax a : ℝ} (hg : 0 ≤ g) (hQ : 0 ≤ Q)
    (ha : 0 < a) (hadef : a = Q * (rhoMax - g) - d) :
    0 < Q * rhoMax - d := by
  have hQg : (0 : ℝ) ≤ Q * g := mul_nonneg hQ hg
  rw [power_exponent_eq hadef]
  linarith only [hQg, ha]

/-! ## The target multiplicity -/

/-! ## The centered kernels -/

/-- **The boundary kernel carrying a fluctuation to the target scale.**  The
boundary coefficient taking a source of scale `r` to a target of scale `j`
inside the scale-`n` terminal cell is the target multiplicity against the
boundary square weight `3^{-((d+1)/2)(j-r)}`.  With the two terminal scales related by
`t = n + ℓ₀`, that product is exactly the printed coefficient: the buffer
factor `3^{aℓ₀/Q}`, the growth weight `3^{-g(n-j)}`, the summable boundary
weight of exponent `(d+1)/2 - a/Q`, and the normalization `3^{-a(t-r)/Q}`
carried by `u_r`. -/
theorem boundary_kernel {d g Q a : ℝ} (hQ : 0 < Q) (l0 n t j r : ℝ)
    (ht : t = n + l0) :
    (3 : ℝ) ^ (-(g + a / Q) * (n - j)) * (3 : ℝ) ^ (-((d + 1) / 2) * (j - r)) =
      (3 : ℝ) ^ (a * l0 / Q) * (3 : ℝ) ^ (-g * (n - j)) *
        (3 : ℝ) ^ (-((d + 1) / 2 - a / Q) * (j - r)) *
        (3 : ℝ) ^ (-a * (t - r) / Q) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  subst ht
  rw [← Real.rpow_add h3, ← Real.rpow_add h3, ← Real.rpow_add h3,
    ← Real.rpow_add h3]
  congr 1
  field_simp
  ring

/-! ## The target coefficient of the centered history -/

/-- **The `Q`-th power target coefficient is paid by the nonlinear row
weight.**  The coefficient `3^{-(Qρ_max-d)(n-j)}` of the positive-gap term in
the centered history is `3^{-(Qg+a)(n-j)}`, and `Qg` is nonnegative, so it is
dominated by the row weight `3^{-a(n-1-j)}` at every target scale below the
terminal one, including the terminal scale itself. -/
theorem power_weight_le_row_weight {d g Q rhoMax a : ℝ} (hg : 0 ≤ g)
    (hQ : 0 ≤ Q) (ha : 0 < a) (hadef : a = Q * (rhoMax - g) - d) {n j : ℝ}
    (hjn : j ≤ n) :
    (3 : ℝ) ^ (-(Q * rhoMax - d) * (n - j)) ≤ (3 : ℝ) ^ (-a * (n - 1 - j)) := by
  have hQg : (0 : ℝ) ≤ Q * g * (n - j) :=
    mul_nonneg (mul_nonneg hQ hg) (by linarith only [hjn])
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [power_exponent_eq hadef]
  linarith only [hQg, ha]

end

end Transport
end HighContrast
end Homogenization
