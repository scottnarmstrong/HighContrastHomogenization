/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.DiscreteConvolution

/-!
# The discrete Young step of the grid transport

The centered rows of the transported history are convolutions: a target scale
reads every source scale below it through the geometric boundary kernel, and
the whole family of rows is then measured in the `Q`-th power.  The step that
turns the rows into a single sum over source scales is the discrete Young
inequality for the pairing of a summable kernel with a `Q`-summable family,
proved here in the two forms the transport uses.

The first form is linear.  Summing the kernel against a nonnegative family and
then over the target scales costs exactly the total kernel weight
`(1 - 3^{-c})^{-1}`, because the sums may be exchanged and the kernel is
summable in the target scale for each fixed source scale.  This is the form
that pays a first-moment row.

The second form is the `Q`-th power one.  For a single target scale the
weighted power mean inequality replaces the `Q`-th power of a kernel average by
the kernel average of `Q`-th powers, at the cost of the total kernel weight to
the power `Q - 1`; the linear form then pays one further weight, and the two
combine into the full `Q`-th power of the total weight.  This is the estimate
behind the contribution of the fluctuations at the new scales: the boundary
kernel is summable because `(d+1)/2 - a/Q` is positive, and its total weight is
the constant the
display calls `C`.

Rows are indexed by an arbitrary finite family of source scales attached to
each target scale, subject only to lying below the target and inside the
ambient source range, because the transport's rows stop at the auxiliary depth
rather than at the target.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

/-! ## Exchanging the two scales -/

/-- A double sum over target scales and their rows of source scales is a double
sum over source scales and the target scales whose row contains them. -/
private theorem sum_row_comm {f : ℤ → ℤ → ℝ} {s t : Finset ℤ} {v : ℤ → Finset ℤ}
    (hv : ∀ j ∈ s, v j ⊆ t) :
    ∑ j ∈ s, ∑ r ∈ v j, f j r =
      ∑ r ∈ t, ∑ j ∈ s.filter fun j => r ∈ v j, f j r := by
  classical
  have hleft : ∀ j ∈ s,
      ∑ r ∈ v j, f j r = ∑ r ∈ t, if r ∈ v j then f j r else 0 := by
    intro j hj
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hv j hj)]
  rw [Finset.sum_congr rfl hleft, Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm

/-! ## The linear form -/

/-- **The discrete Young step, first-moment form.**  A nonnegative family read
through the geometric kernel along the rows, summed over the target scales,
is at most the total kernel weight times the sum of the family. -/
theorem sum_kernel_le {c : ℝ} (hc : 0 < c) {s t : Finset ℤ} {v : ℤ → Finset ℤ}
    (hv : ∀ j ∈ s, v j ⊆ t) (hvle : ∀ j ∈ s, ∀ r ∈ v j, r ≤ j) (x : ℤ → ℝ)
    (hx : ∀ r, 0 ≤ x r) :
    ∑ j ∈ s, ∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * x r ≤
      1 / (1 - (3 : ℝ) ^ (-c)) * ∑ r ∈ t, x r := by
  classical
  rw [sum_row_comm hv, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hx r)
  refine sum_geom_above_le hc r _ fun j hj => ?_
  obtain ⟨hjs, hjv⟩ := Finset.mem_filter.mp hj
  exact hvle j hjs r hjv

/-! ## The weighted power mean at one target scale -/

/-- The `Q`-th power of a positively weighted average is at most the weighted
average of the `Q`-th powers, up to the total weight to the power `Q - 1`.
This is the weighted power mean inequality, normalized so that the total weight
appears explicitly. -/
private theorem rpow_sum_weight_le {Q kappa : ℝ} (hQ : 1 ≤ Q)
    (K u : ℤ → ℝ) (hK : ∀ r, 0 < K r) (hu : ∀ r, 0 ≤ u r) (w : Finset ℤ)
    (hsum : ∑ r ∈ w, K r ≤ kappa) :
    (∑ r ∈ w, K r * u r) ^ Q ≤ kappa ^ (Q - 1) * ∑ r ∈ w, K r * u r ^ Q := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  rcases w.eq_empty_or_nonempty with rfl | hne
  · simp [Real.zero_rpow (ne_of_gt hQ0)]
  have hW : (0 : ℝ) < ∑ r ∈ w, K r := Finset.sum_pos (fun r _ => hK r) hne
  have hnum : (0 : ℝ) ≤ ∑ r ∈ w, K r * u r :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hK r).le (hu r)
  have hpow : (0 : ℝ) ≤ ∑ r ∈ w, K r * u r ^ Q :=
    Finset.sum_nonneg fun r _ =>
      mul_nonneg (hK r).le (Real.rpow_nonneg (hu r) Q)
  have hw1 : ∑ r ∈ w, K r / (∑ q ∈ w, K q) = 1 := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hW)
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow w
    (fun r => K r / (∑ q ∈ w, K q)) u
    (fun r _ => div_nonneg (hK r).le hW.le) hw1 (fun r _ => hu r) hQ
  have hleft : ∑ r ∈ w, K r / (∑ q ∈ w, K q) * u r =
      (∑ r ∈ w, K r * u r) / (∑ q ∈ w, K q) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hright : ∑ r ∈ w, K r / (∑ q ∈ w, K q) * u r ^ Q =
      (∑ r ∈ w, K r * u r ^ Q) / (∑ q ∈ w, K q) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hleft, hright, Real.div_rpow hnum hW.le,
    div_le_iff₀ (Real.rpow_pos_of_pos hW Q)] at hmean
  have hstep : (∑ r ∈ w, K r * u r) ^ Q ≤
      (∑ q ∈ w, K q) ^ (Q - 1) * ∑ r ∈ w, K r * u r ^ Q := by
    refine le_trans hmean (le_of_eq ?_)
    rw [Real.rpow_sub hW, Real.rpow_one]
    ring
  refine le_trans hstep (mul_le_mul_of_nonneg_right ?_ hpow)
  exact Real.rpow_le_rpow hW.le hsum (by linarith only [hQ])

/-! ## The `Q`-th power form -/

/-- **The discrete Young step, `Q`-th power form.**  Each target row is a
kernel average of a nonnegative family; the `Q`-th powers of the rows sum to at
most the `Q`-th power of the total kernel weight times the sum of the `Q`-th
powers of the family.  This is the convolution behind the contribution of the
fluctuations at the new scales. -/
theorem sum_rpow_kernel_le {c Q : ℝ} (hc : 0 < c) (hQ : 1 ≤ Q) {s t : Finset ℤ}
    {v : ℤ → Finset ℤ} (hv : ∀ j ∈ s, v j ⊆ t)
    (hvle : ∀ j ∈ s, ∀ r ∈ v j, r ≤ j) (u : ℤ → ℝ) (hu : ∀ r, 0 ≤ u r) :
    ∑ j ∈ s, (∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r) ^ Q ≤
      (1 / (1 - (3 : ℝ) ^ (-c))) ^ Q * ∑ r ∈ t, u r ^ Q := by
  classical
  have hr1 : (3 : ℝ) ^ (-c) < 1 := PortableHistory.geom_ratio_lt_one hc
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-c) := by linarith only [hr1]
  have hk0 : (0 : ℝ) < 1 / (1 - (3 : ℝ) ^ (-c)) := by positivity
  have hrow : ∀ j ∈ s,
      (∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r) ^ Q ≤
        (1 / (1 - (3 : ℝ) ^ (-c))) ^ (Q - 1) *
          ∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r ^ Q := by
    intro j hj
    refine rpow_sum_weight_le hQ _ u
      (fun r => Real.rpow_pos_of_pos (by norm_num) _) hu _ ?_
    exact sum_geom_below_le hc j _ fun r hr => hvle j hj r hr
  refine le_trans (Finset.sum_le_sum hrow) ?_
  rw [← Finset.mul_sum]
  have hlin := sum_kernel_le hc hv hvle (fun r => u r ^ Q)
    fun r => Real.rpow_nonneg (hu r) Q
  have hfinal : (1 / (1 - (3 : ℝ) ^ (-c))) ^ (Q - 1) *
      (1 / (1 - (3 : ℝ) ^ (-c)) * ∑ r ∈ t, u r ^ Q) =
      (1 / (1 - (3 : ℝ) ^ (-c))) ^ Q * ∑ r ∈ t, u r ^ Q := by
    rw [← mul_assoc]
    congr 1
    nth_rewrite 2 [← Real.rpow_one (1 / (1 - (3 : ℝ) ^ (-c)))]
    rw [← Real.rpow_add hk0]
    congr 1
    ring
  refine le_trans (mul_le_mul_of_nonneg_left hlin
    (Real.rpow_nonneg hk0.le _)) (le_of_eq hfinal)

/-! ## The fresh centered rows -/

/-- **The contribution of the fluctuations at the new scales, at the scalar
level.**  Each fresh target row is, at the level of the `Q`-th root, the buffer
factor `3^{aℓ₀/Q}` times the growth weight times the summable boundary kernel
applied to the normalized moments.  The growth weight is at most one below the
terminal scale, so the `Q`-th powers of the rows sum to the buffer factor
`3^{aℓ₀}` times the
`Q`-th power of the total kernel weight times the sum of the `Q`-th powers of
the moments. -/
theorem fresh_rows_le {c Q g a l0 : ℝ} (hc : 0 < c) (hQ : 1 ≤ Q) (hg : 0 ≤ g)
    {n : ℤ} {s t : Finset ℤ} {v : ℤ → Finset ℤ} (hv : ∀ j ∈ s, v j ⊆ t)
    (hvle : ∀ j ∈ s, ∀ r ∈ v j, r ≤ j) (hsn : ∀ j ∈ s, j ≤ n) (u y : ℤ → ℝ)
    (hu : ∀ r, 0 ≤ u r) (hy : ∀ j ∈ s, 0 ≤ y j)
    (hrow : ∀ j ∈ s, y j ≤ ∑ r ∈ v j,
      (3 : ℝ) ^ (a * l0 / Q) * (3 : ℝ) ^ (-g * ((n : ℝ) - (j : ℝ))) *
        ((3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r)) :
    ∑ j ∈ s, y j ^ Q ≤
      (3 : ℝ) ^ (a * l0) * (1 / (1 - (3 : ℝ) ^ (-c))) ^ Q * ∑ r ∈ t, u r ^ Q := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hconst : ((3 : ℝ) ^ (a * l0 / Q)) ^ Q = (3 : ℝ) ^ (a * l0) := by
    rw [← Real.rpow_mul h3.le]
    congr 1
    field_simp
  have hstep : ∀ j ∈ s, y j ^ Q ≤ (3 : ℝ) ^ (a * l0) *
      (∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r) ^ Q := by
    intro j hj
    have hS : (0 : ℝ) ≤ ∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r :=
      Finset.sum_nonneg fun r _ => mul_nonneg (Real.rpow_nonneg h3.le _) (hu r)
    have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn j hj
    have hgrowth : (3 : ℝ) ^ (-g * ((n : ℝ) - (j : ℝ))) ≤ 1 := by
      have hpos : (0 : ℝ) ≤ g * ((n : ℝ) - (j : ℝ)) :=
        mul_nonneg hg (by linarith only [hjn])
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by linarith only [hpos])
    have hrowj := hrow j hj
    rw [← Finset.mul_sum] at hrowj
    have hbound : y j ≤ (3 : ℝ) ^ (a * l0 / Q) *
        ∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r := by
      refine le_trans hrowj (mul_le_mul_of_nonneg_right ?_ hS)
      calc (3 : ℝ) ^ (a * l0 / Q) * (3 : ℝ) ^ (-g * ((n : ℝ) - (j : ℝ)))
          ≤ (3 : ℝ) ^ (a * l0 / Q) * 1 :=
            mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg h3.le _)
        _ = (3 : ℝ) ^ (a * l0 / Q) := mul_one _
    calc y j ^ Q
        ≤ ((3 : ℝ) ^ (a * l0 / Q) *
            ∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r) ^ Q :=
          Real.rpow_le_rpow (hy j hj) hbound hQ0.le
      _ = ((3 : ℝ) ^ (a * l0 / Q)) ^ Q *
            (∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r) ^ Q :=
          Real.mul_rpow (Real.rpow_nonneg h3.le _) hS
      _ = (3 : ℝ) ^ (a * l0) *
            (∑ r ∈ v j, (3 : ℝ) ^ (-c * ((j : ℝ) - (r : ℝ))) * u r) ^ Q := by
          rw [hconst]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left (sum_rpow_kernel_le hc hQ hv hvle u hu)
    (Real.rpow_nonneg h3.le _)

end

end Transport
end HighContrast
end Homogenization
