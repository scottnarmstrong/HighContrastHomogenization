/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredBound
import HCPoly.Provider.Transport.CenteredAncestor
import HCPoly.Provider.Transport.YoungConvolution

/-!
# The principal upper bound of the centered transport

The centered half of `p.two.grid.transport` reaches its target in
three printed displays: the sources strictly above the checkpoint are summed by
discrete Young convolution into the contribution of the fluctuations at the new
scales, those at or below it are grouped by their scale-`b` ancestor into
`e.two.grid.old.history.factor`, and the two together are the combined bound for
the transported fluctuations.

All three are written at the level of the `Q`-th root, and the passage to the
`Q`-th power is the cost of replacing the maximum over target cells by a sum: the
terminal weight `3^{-ρ_max(n-j)}` and the `Q`-th root of the number `3^{d(n-j)}`
of scale-`j` cells in the terminal cell combine into `3^{-(g+a/Q)(n-j)}`, whose
`Q`-th power is the target coefficient the estimate is summed against.  A
boundary source is carried to the target scale by the boundary kernel, summable
because `(d+1)/2 - a/Q > 0`; a bulk source by the adaptive bulk kernel, where the
summation is the multiplicity of `j ↦ j - λ_j`, at most two.  Both leave one
buffer factor `3^{aℓ₀}`, and the inherited root coefficient is raised to the
power `Q` exactly, which is what turns the operator norm of the relative mean at
the checkpoint into the gain `1 + 𝔥_Q(P_{b,t}^q)` the portable profile carries.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The target multiplicity -/

/-- **The cost of replacing the maximum over target cells by a sum**, at the
level of the `Q`-th power.  A quantity carrying the root weight `3^{-(g+a/Q)s}`
has `Q`-th power carrying the printed target coefficient `3^{-(Qρ_max-d)s}`. -/
private theorem target_weight_rpow {Q g rhoMax a : ℝ} (hQ : 0 < Q)
    (hadef : a = Q * (rhoMax - g) - (d : ℝ)) (s : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ((3 : ℝ) ^ (-(g + a / Q) * s) * x) ^ Q =
      (3 : ℝ) ^ (-(Q * rhoMax - (d : ℝ)) * s) * x ^ Q := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  have hexp : -(g + a / Q) * s * Q = -(Q * rhoMax - (d : ℝ)) * s := by
    rw [power_exponent_eq (d := (d : ℝ)) (g := g) (Q := Q) (rhoMax := rhoMax) hadef]
    field_simp
  rw [Real.mul_rpow (Real.rpow_nonneg h3.le _) hx, ← Real.rpow_mul h3.le, hexp]

/-! ## The fresh rows -/

/-- **The contribution of the fluctuations at the new scales, the boundary
half.**  The hypothesis is the printed row: the `ℓ²` square weight
`3^{(d+1)(r-j)/2}` of the square-weight bound for the boundary cells against the
sharp normalization `e^{Δ_{r,t}^q}v_r^q` of the change of normalization to the
terminal generation.  The
exhibited constant `(1 - 3^{-((d+1)/2-a/Q)})^{-Q}` is finite exactly because the
boundary exponent is positive. -/
theorem fresh_centered_boundary_le {P : Measure (CoeffSpace d)} {q : Mat d}
    {Q g rhoMax a : ℝ} (hQ : 1 ≤ Q) (hg : 0 ≤ g)
    (hadef : a = Q * (rhoMax - g) - (d : ℝ))
    (hc : 0 < ((d : ℝ) + 1) / 2 - a / Q) {l0 n t : ℤ}
    (ht : (t : ℝ) = (n : ℝ) + (l0 : ℝ)) {s T : Finset ℤ} {v : ℤ → Finset ℤ}
    (hv : ∀ j ∈ s, v j ⊆ T) (hvle : ∀ j ∈ s, ∀ r ∈ v j, r ≤ j) (hsn : ∀ j ∈ s, j ≤ n)
    {f vr : ℤ → ℝ} (hvr : ∀ r, 0 ≤ vr r) (hf : ∀ j ∈ s, 0 ≤ f j)
    (hrow : ∀ j ∈ s, f j ≤ ∑ r ∈ v j,
      (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2) * ((j : ℝ) - (r : ℝ))) *
        (Real.exp (detIncrement P q r t) * vr r)) :
    ∑ j ∈ s, (3 : ℝ) ^ (-(Q * rhoMax - (d : ℝ)) * ((n : ℝ) - (j : ℝ))) * f j ^ Q ≤
      (3 : ℝ) ^ (a * (l0 : ℝ)) *
          (1 / (1 - (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2 - a / Q)))) ^ Q *
        ∑ r ∈ T, (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
          Real.exp (Q * detIncrement P q r t) * vr r ^ Q := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  -- the printed row is the engine's row, by the boundary kernel identity
  have hyrow : ∀ j ∈ s, (3 : ℝ) ^ (-(g + a / Q) * ((n : ℝ) - (j : ℝ))) * f j ≤
      ∑ r ∈ v j, (3 : ℝ) ^ (a * (l0 : ℝ) / Q) * (3 : ℝ) ^ (-g * ((n : ℝ) - (j : ℝ))) *
        ((3 : ℝ) ^ (-(((d : ℝ) + 1) / 2 - a / Q) * ((j : ℝ) - (r : ℝ))) *
          ((3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ)) / Q) *
            (Real.exp (detIncrement P q r t) * vr r))) := by
    intro j hj
    refine le_trans (mul_le_mul_of_nonneg_left (hrow j hj)
      (Real.rpow_nonneg h3.le (-(g + a / Q) * ((n : ℝ) - (j : ℝ))))) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => le_of_eq ?_
    have hk := boundary_kernel (d := (d : ℝ)) (g := g) (Q := Q) (a := a) hQ0
      (l0 : ℝ) (n : ℝ) (t : ℝ) (j : ℝ) (r : ℝ) ht
    linear_combination (Real.exp (detIncrement P q r t) * vr r) * hk
  have hmain := fresh_rows_le (c := ((d : ℝ) + 1) / 2 - a / Q) (Q := Q) (g := g)
    (a := a) (l0 := (l0 : ℝ)) hc hQ hg hv hvle hsn
    (fun r => (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ)) / Q) *
      (Real.exp (detIncrement P q r t) * vr r))
    (fun j => (3 : ℝ) ^ (-(g + a / Q) * ((n : ℝ) - (j : ℝ))) * f j)
    (fun r => mul_nonneg (Real.rpow_nonneg h3.le _)
      (mul_nonneg (Real.exp_nonneg _) (hvr r)))
    (fun j hj => mul_nonneg (Real.rpow_nonneg h3.le _) (hf j hj)) hyrow
  -- the two power identities
  have hyQ : ∀ j ∈ s,
      ((3 : ℝ) ^ (-(g + a / Q) * ((n : ℝ) - (j : ℝ))) * f j) ^ Q =
      (3 : ℝ) ^ (-(Q * rhoMax - (d : ℝ)) * ((n : ℝ) - (j : ℝ))) * f j ^ Q := fun j hj =>
    target_weight_rpow hQ0 hadef _ (hf j hj)
  have huQ : ∀ r : ℤ, ((3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ)) / Q) *
        (Real.exp (detIncrement P q r t) * vr r)) ^ Q =
      (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) * Real.exp (Q * detIncrement P q r t) *
        vr r ^ Q := by
    intro r
    rw [Real.mul_rpow (Real.rpow_nonneg h3.le _)
        (mul_nonneg (Real.exp_nonneg _) (hvr r)),
      Real.mul_rpow (Real.exp_nonneg _) (hvr r), ← Real.rpow_mul h3.le,
      ← Real.exp_mul, mul_comm (detIncrement P q r t) Q,
      show -a * ((t : ℝ) - (r : ℝ)) / Q * Q = -a * ((t : ℝ) - (r : ℝ)) from by
        field_simp]
    ring
  refine le_trans (le_of_eq (Finset.sum_congr rfl hyQ).symm) (le_trans hmain ?_)
  exact le_of_eq (by rw [Finset.sum_congr rfl fun r (_ : r ∈ T) => huQ r])

/-! ## The inherited coefficient -/

/-- **`e.two.grid.old.history.factor`, its coefficient.**  The root
coefficient of the inherited rows, raised to the power `Q`, is the printed
inherited coefficient `3^{aℓ₀}3^{-a(t-b)}(1+𝔥_Q(P_{b,t}^q))`; both steps are
exact. -/
theorem inherited_coefficient_le {g Q rhoMax a l0 : ℝ} (hg : 0 ≤ g) (hQ : 0 < Q)
    (hadef : a = Q * (rhoMax - g) - (d : ℝ)) {n b t : ℤ} (hbn : b ≤ n)
    (ht : (t : ℝ) = (n : ℝ) + l0) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    ((3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) * ((n : ℝ) - (b : ℝ))) *
        ‖toFullBlockMat Pm‖) ^ Q ≤
      (3 : ℝ) ^ (a * l0) * (3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) * (1 + frakH Q Pm) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hbase : (0 : ℝ) ≤
      (3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) * ((n : ℝ) - (b : ℝ))) * ‖toFullBlockMat Pm‖ :=
    mul_nonneg (Real.rpow_nonneg h3.le _) (norm_nonneg _)
  refine le_trans (Real.rpow_le_rpow hbase
    (root_coefficient_le hg hQ hadef hbn ht hPm) hQ.le) ?_
  exact le_of_eq (inherited_coefficient_eq hQ hPm)

/-! ## The principal upper bound -/

end

end Transport
end HighContrast
end Homogenization
