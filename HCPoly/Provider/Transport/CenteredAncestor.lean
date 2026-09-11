/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.DiscreteConvolution
import HCPoly.Provider.Transport.GapComparison
import HCPoly.Provider.Transport.GapFunctions

/-!
# The inherited rows of the centered estimate

The sources of the transport that lie at or below the checkpoint are not
restarted: they are grouped by their scale-`b` ancestor, and the whole history
they carry is read off the single statistic `X_B` attached to that ancestor,
which stationarity compares with the centered history at the checkpoint.  What
has to be paid is the arithmetic of the grouping, and this file proves it: the
row sum inside an ancestor at the checkpoint generation, the two envelopes that
follow from it, the step that forces the auxiliary depth to be one on an
inherited bulk, and the root coefficient of `e.two.grid.old.history.factor`.

The ancestor sum is where `ρ_max < 1` is essential and nowhere else.  Inside a
fixed ancestor the codimension-one row of scale `r` has relative weight `3^{r-j}`
and its history is renormalized from scale `r` to scale `b` at the cost
`3^{ρ_max(b-r)}`; the product is `3^{b-j}3^{-(1-ρ_max)(b-r)}`, and the geometric
series in `b - r` converges exactly because the maximal weight is strictly below
one.  Restricting the row to the scales the boundary filling actually uses,
`r ≤ j - λ_j`, improves the same computation by the factor `3^{-(1-ρ_max)λ_j}`,
which is at most one; that is the printed envelope `C3^{ρ_max(b-j)}` for `j < b`,
while for `j ≥ b` the unrestricted sum already gives `C3^{b-j}`.

The root coefficient is the identity `ρ_max - d/Q = g + a/Q` behind the cost of
replacing the maximum over target cells by a sum, together with
`‖P‖ ≤ 1 + tr(P-I)`:
the growth exponent is discarded, the two terminal scales are exchanged through
`t = n + ℓ₀`, and the operator norm of the relative mean is exactly the `Q`-th
root of `1 + 𝔥_Q`, so the printed coefficient is reached with no loss.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

/-! ## The ancestor sum -/

/-- **The row sum inside an ancestor at the checkpoint generation.**  Inside a
fixed scale-`b` ancestor the codimension-one rows of all the scales at or below
the checkpoint, each weighted by its relative volume `3^{r-j}` and renormalized
to the checkpoint at the cost `3^{ρ_max(b-r)}`, total at most
`C_{ρ_max}3^{b-j}`.

The exhibited constant is `(1 - 3^{-(1-ρ_max)})^{-1}`, and the strict bound
`ρ_max < 1` is what makes it finite. -/
theorem ancestor_sum_le {rhoMax : ℝ} (hrho : rhoMax < 1) (jStar b j : ℤ) :
    ∑ r ∈ Finset.Icc jStar b,
        (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax))) * (3 : ℝ) ^ ((b : ℝ) - (j : ℝ)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hc : (0 : ℝ) < 1 - rhoMax := by linarith only [hrho]
  have hterm : ∀ r : ℤ,
      (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) =
        (3 : ℝ) ^ ((b : ℝ) - (j : ℝ)) *
          (3 : ℝ) ^ (-(1 - rhoMax) * ((b : ℝ) - (r : ℝ))) := by
    intro r
    rw [← Real.rpow_add h3, ← Real.rpow_add h3]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (sum_geom_below_le hc b _ fun r hr => (Finset.mem_Icc.mp hr).2)
    (Real.rpow_nonneg h3.le _)

/-- **The inherited boundary row of a continued target level.**  The boundary
filling of a scale-`j` target uses only the scales at or below `j - λ_j`, and
restricting the ancestor sum to that range improves the bound by the factor
`3^{-(1-ρ_max)λ_j}`, leaving the printed envelope `C3^{ρ_max(b-j)}` before the
depth is discarded. -/
theorem ancestor_row_le {rhoMax : ℝ} (hrho : rhoMax < 1) (jStar b j lam : ℤ) :
    ∑ r ∈ Finset.Icc jStar (j - lam),
        (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax))) *
        ((3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ))) *
          (3 : ℝ) ^ (-(1 - rhoMax) * (lam : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hc : (0 : ℝ) < 1 - rhoMax := by linarith only [hrho]
  have hterm : ∀ r : ℤ,
      (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) =
        (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ))) *
          (3 : ℝ) ^ (-(1 - rhoMax) * (lam : ℝ)) *
          (3 : ℝ) ^ (-(1 - rhoMax) * (((j - lam : ℤ) : ℝ) - (r : ℝ))) := by
    intro r
    rw [← Real.rpow_add h3, ← Real.rpow_add h3, ← Real.rpow_add h3]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (sum_geom_below_le hc (j - lam) _ fun r hr => (Finset.mem_Icc.mp hr).2)
    (by positivity)

/-! ## The auxiliary depth on an inherited bulk -/

/-! ## The root coefficient -/

/-- **The `Q`-th root of the gain is the trace gap.**  For a block above the
identity, `1 + 𝔥_Q(P) = (1 + tr(P-I))^Q`, so the `Q`-th root of `1 + 𝔥_Q(P)` is
exactly `1 + tr(P-I)`. -/
theorem one_add_frakH_rpow_inv {d : ℕ} {Q : ℝ} (hQ : 0 < Q) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    (1 + frakH Q Pm) ^ Q⁻¹ = 1 + (blockTrace Pm - 2 * (d : ℝ)) := by
  have hgap : (0 : ℝ) ≤ blockTrace Pm - 2 * (d : ℝ) := zero_le_trace_gap hPm
  have hbase : (0 : ℝ) ≤ 1 + (blockTrace Pm - 2 * (d : ℝ)) := by linarith only [hgap]
  have hval : 1 + frakH Q Pm = (1 + (blockTrace Pm - 2 * (d : ℝ))) ^ Q := by
    rw [frakH]
    ring
  rw [hval, ← Real.rpow_mul hbase, mul_inv_cancel₀ (ne_of_gt hQ), Real.rpow_one]

/-- **The root coefficient of the inherited rows.**  The terminal weight of a
scale-`b` ancestor inside the scale-`n` target, discounted by the target
multiplicity and multiplied by the operator norm of the relative mean, is at
most the buffer factor `3^{aℓ₀/Q}` times the terminal weight `3^{-a(t-b)/Q}`
times the `Q`-th root of `1 + 𝔥_Q(P_{b,t}^q)`.

Both inputs are exact: `ρ_max - d/Q = g + a/Q` is the defining relation of the
derived exponent, and `‖P‖_op ≤ 1 + tr(P-I) = (1 + 𝔥_Q(P))^{1/Q}`.  The only
inequality is discarding the growth weight `3^{-g(n-b)}`, which is at most one
because the checkpoint lies below the new terminal scale. -/
theorem root_coefficient_le {d : ℕ} {g Q rhoMax a l0 : ℝ} (hg : 0 ≤ g) (hQ : 0 < Q)
    (hadef : a = Q * (rhoMax - g) - (d : ℝ)) {n b t : ℤ} (hbn : b ≤ n)
    (ht : (t : ℝ) = (n : ℝ) + l0) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    (3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) * ((n : ℝ) - (b : ℝ))) * ‖toFullBlockMat Pm‖ ≤
      (3 : ℝ) ^ (a * l0 / Q) * (3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ)) / Q) *
        (1 + frakH Q Pm) ^ Q⁻¹ := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hbnR : (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbn
  have hnorm : ‖toFullBlockMat Pm‖ ≤ (1 + frakH Q Pm) ^ Q⁻¹ := by
    rw [one_add_frakH_rpow_inv hQ hPm]
    exact norm_le_one_add_trace_gap hPm
  have hroot : (0 : ℝ) ≤ (1 + frakH Q Pm) ^ Q⁻¹ := by
    rw [one_add_frakH_rpow_inv hQ hPm]
    have := zero_le_trace_gap hPm
    linarith only [this]
  have hexp : (3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) * ((n : ℝ) - (b : ℝ))) ≤
      (3 : ℝ) ^ (a * l0 / Q) * (3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ)) / Q) := by
    rw [← Real.rpow_add h3, root_exponent_eq hQ hadef]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hgrowth : (0 : ℝ) ≤ g * ((n : ℝ) - (b : ℝ)) :=
      mul_nonneg hg (by linarith only [hbnR])
    rw [ht]
    have hQne : Q ≠ 0 := ne_of_gt hQ
    have hsplit : a * l0 / Q + -a * ((n : ℝ) + l0 - (b : ℝ)) / Q -
        -(g + a / Q) * ((n : ℝ) - (b : ℝ)) = g * ((n : ℝ) - (b : ℝ)) := by
      field_simp
      ring
    linarith only [hgrowth, hsplit]
  have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ (-(rhoMax - (d : ℝ) / Q) * ((n : ℝ) - (b : ℝ))) :=
    Real.rpow_nonneg h3.le _
  have hcoef : (0 : ℝ) ≤ (3 : ℝ) ^ (a * l0 / Q) * (3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ)) / Q) :=
    mul_nonneg (Real.rpow_nonneg h3.le _) (Real.rpow_nonneg h3.le _)
  exact mul_le_mul hexp hnorm (norm_nonneg _) hcoef

/-- **The inherited coefficient at the level of the `Q`-th power**, the
coefficient of `e.two.grid.old.history.factor`.  Raising the root
coefficient to the power `Q` turns the buffer factor into `3^{aℓ₀}`, the
terminal weight into `3^{-a(t-b)}` and the `Q`-th root of the gain back into
`1 + 𝔥_Q(P_{b,t}^q)`. -/
theorem inherited_coefficient_eq {d : ℕ} {Q a l0 : ℝ} (hQ : 0 < Q) {b t : ℤ}
    {Pm : BlockMat d} (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    ((3 : ℝ) ^ (a * l0 / Q) * (3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ)) / Q) *
        (1 + frakH Q Pm) ^ Q⁻¹) ^ Q =
      (3 : ℝ) ^ (a * l0) * (3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
        (1 + frakH Q Pm) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hgap : (0 : ℝ) ≤ blockTrace Pm - 2 * (d : ℝ) := zero_le_trace_gap hPm
  have hfin : (0 : ℝ) ≤ 1 + frakH Q Pm := by
    rw [frakH]
    have h1 : (1 : ℝ) ^ Q ≤ (1 + (blockTrace Pm - 2 * (d : ℝ))) ^ Q :=
      Real.rpow_le_rpow zero_le_one (by linarith only [hgap]) hQ.le
    rw [Real.one_rpow] at h1
    linarith only [h1]
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hfin _),
    Real.mul_rpow (Real.rpow_nonneg h3.le _) (Real.rpow_nonneg h3.le _),
    ← Real.rpow_mul h3.le, ← Real.rpow_mul h3.le, ← Real.rpow_mul hfin,
    inv_mul_cancel₀ (ne_of_gt hQ), Real.rpow_one]
  congr 2 <;> field_simp

end

end Transport
end HighContrast
end Homogenization
