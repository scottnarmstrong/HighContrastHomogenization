/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The convexity of the gain function

The proof of `p.two.grid.transport` isolates one matrix
calculation and uses it at every target cell.  Its first half is the convexity
bound for the mean penalty: if the relative means
`P_α ≥ I` are combined with nonnegative weights `θ_α` of total mass at most one
and the deficit is filled with the identity,
`P̄ = Σ_α θ_α P_α + (1 - m)I`, then the gain function does not increase,
`𝔥_Q(P̄) ≤ Σ_α θ_α 𝔥_Q(P_α)`.

The gain function `𝔥_Q(P) = (1 + tr(P - I))^Q - 1` reads the block only through
the scalar `tr(P - I)`, and the filling makes that scalar the same convex
combination: `tr(P̄ - I) = Σ_α θ_α tr(P_α - I)`.  So the display is the
statement that `t ↦ (1 + t)^Q - 1` is convex on the nonnegative reals and
vanishes at zero, applied to a subprobability weight vector.  That is proved
here in two steps — a two point comparison and a normalized one — and both are
instances of the weighted power mean inequality.

The two point comparison is recorded separately because the transport uses it a
second time, on its own: it is the bound `(1 + t)^Q - 1 ≤ (t/T)((1 + T)^Q - 1)`
that turns the bridge error into an additive term, and there the roles of the
two arguments are reversed.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix

noncomputable section

/-! ## The two scalar convexity steps -/

/-- **The two point step.**  For an exponent at least one, a weight in the unit
interval and a nonnegative argument, the power of the interpolation is below the
interpolation of the powers.  This is the weighted power mean inequality on two
points. -/
theorem rpow_two_point {Q m y : ℝ} (hQ : 1 ≤ Q) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hy : 0 ≤ y) : (m * y + (1 - m)) ^ Q ≤ m * y ^ Q + (1 - m) := by
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ ![m, 1 - m] i := by
    intro i _
    fin_cases i
    · exact hm
    · show (0 : ℝ) ≤ 1 - m
      linarith only [hm1]
  have hw' : ∑ i ∈ (Finset.univ : Finset (Fin 2)), ![m, 1 - m] i = 1 := by
    simp [Fin.sum_univ_two]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ ![y, 1] i := by
    intro i _
    fin_cases i
    · exact hy
    · exact zero_le_one
  have hmain := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.univ : Finset (Fin 2))
    ![m, 1 - m] ![y, 1] hw hw' hz hQ
  simpa [Fin.sum_univ_two, Real.one_rpow] using hmain

/-- **The gain of a scaled argument.**  The gain function
`t ↦ (1 + t)^Q - 1` vanishes at zero and is convex, so it is subhomogeneous:
scaling the argument by a weight in the unit interval scales the gain by at
most that weight. -/
theorem rpow_sub_one_smul_le {Q m u : ℝ} (hQ : 1 ≤ Q) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hu : 0 ≤ u) : (1 + m * u) ^ Q - 1 ≤ m * ((1 + u) ^ Q - 1) := by
  have hrw : 1 + m * u = m * (1 + u) + (1 - m) := by ring
  have hstep := rpow_two_point (y := 1 + u) hQ hm hm1 (by linarith only [hu])
  rw [hrw]
  linarith only [hstep]

/-- **The gain is dominated by its value at a larger argument.**  For
`0 ≤ t ≤ T` the gain at `t` is at most the fraction `t/T` of the gain at `T`;
this is the two point step with weight `t/T`.  It is the form in which the
transport turns a bounded bridge error into an additive term. -/
theorem rpow_sub_one_le_div_mul {Q t T : ℝ} (hQ : 1 ≤ Q) (ht : 0 ≤ t) (htT : t ≤ T)
    (hT : 0 < T) : (1 + t) ^ Q - 1 ≤ t / T * ((1 + T) ^ Q - 1) := by
  have hm : 0 ≤ t / T := div_nonneg ht hT.le
  have hm1 : t / T ≤ 1 := (div_le_one hT).mpr htT
  have hstep := rpow_sub_one_smul_le (u := T) hQ hm hm1 hT.le
  rwa [div_mul_cancel₀ _ hT.ne'] at hstep

/-! ## The convexity display -/

/-- **The subprobability Jensen step.**  For nonnegative weights of total mass at
most one and nonnegative arguments, the gain of the weighted sum is at most the
weighted sum of the gains. -/
theorem rpow_sub_one_sum_le {ι : Type*} (s : Finset ι) {Q : ℝ} (hQ : 1 ≤ Q)
    (theta x : ι → ℝ) (hth : ∀ α ∈ s, 0 ≤ theta α) (hx : ∀ α ∈ s, 0 ≤ x α)
    (hm : ∑ α ∈ s, theta α ≤ 1) :
    (1 + ∑ α ∈ s, theta α * x α) ^ Q - 1 ≤
      ∑ α ∈ s, theta α * ((1 + x α) ^ Q - 1) := by
  set m : ℝ := ∑ α ∈ s, theta α with hmdef
  have hm0 : 0 ≤ m := Finset.sum_nonneg hth
  rcases eq_or_lt_of_le hm0 with hzero | hpos
  · -- all weights vanish
    have hall : ∀ α ∈ s, theta α = 0 := by
      intro α hα
      have := (Finset.sum_eq_zero_iff_of_nonneg hth).mp hzero.symm α hα
      exact this
    have hsum : ∑ α ∈ s, theta α * x α = 0 :=
      Finset.sum_eq_zero fun α hα => by rw [hall α hα, zero_mul]
    have hrhs : ∑ α ∈ s, theta α * ((1 + x α) ^ Q - 1) = 0 :=
      Finset.sum_eq_zero fun α hα => by rw [hall α hα, zero_mul]
    rw [hsum, hrhs, add_zero, Real.one_rpow, sub_self]
  · -- normalize the weights, apply the power mean inequality, then rescale
    have hne : m ≠ 0 := hpos.ne'
    have hw : ∀ α ∈ s, 0 ≤ theta α / m := fun α hα => div_nonneg (hth α hα) hm0
    have hw' : ∑ α ∈ s, theta α / m = 1 := by
      rw [← Finset.sum_div, ← hmdef, div_self hne]
    have hz : ∀ α ∈ s, 0 ≤ 1 + x α := fun α hα => by linarith only [hx α hα]
    have hmain := Real.rpow_arith_mean_le_arith_mean_rpow s (fun α => theta α / m)
      (fun α => 1 + x α) hw hw' hz hQ
    set Y : ℝ := ∑ α ∈ s, theta α / m * (1 + x α) with hY
    set Z : ℝ := ∑ α ∈ s, theta α * (1 + x α) ^ Q with hZ
    have hZm : ∑ α ∈ s, theta α / m * (1 + x α) ^ Q = Z / m := by
      rw [hZ, Finset.sum_div]
      exact Finset.sum_congr rfl fun α _ => by rw [div_mul_eq_mul_div]
    rw [hZm] at hmain
    have hYm : m * Y = m + ∑ α ∈ s, theta α * x α := by
      rw [hY, Finset.mul_sum]
      have hterm : ∀ α ∈ s, m * (theta α / m * (1 + x α)) = theta α + theta α * x α := by
        intro α _
        field_simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← hmdef]
    have hYnn : 0 ≤ Y := Finset.sum_nonneg fun α hα => mul_nonneg (hw α hα) (hz α hα)
    have hstep := rpow_two_point (m := m) (y := Y) hQ hm0 hm hYnn
    have hmY : m * Y ^ Q ≤ Z := by
      have := mul_le_mul_of_nonneg_left hmain hm0
      rwa [mul_div_cancel₀ _ hne] at this
    have hlhs : 1 + ∑ α ∈ s, theta α * x α = m * Y + (1 - m) := by
      rw [hYm]; ring
    have hrhs : ∑ α ∈ s, theta α * ((1 + x α) ^ Q - 1) = Z - m := by
      rw [hZ, hmdef, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hlhs, hrhs]
    linarith only [hstep, hmY]

/-! ## The printed display -/

/-- **The convexity bound for the mean penalty.**  The relative means of the
selected cells are combined with nonnegative weights of total mass at most one,
the deficit being filled with the identity; the gain function of the resulting
block is at most the same weighted combination of the gains.

The hypothesis on `P̄` is the definition of the combination written on the flattened
carrier, and the hypothesis on the `P_α` is that each lies above the identity —
which the transport has from the mean order. -/
theorem positive_packet {d : ℕ} {ι : Type*} (s : Finset ι) {Q : ℝ} (hQ : 1 ≤ Q)
    (theta : ι → ℝ) (hth : ∀ α ∈ s, 0 ≤ theta α) (hm : ∑ α ∈ s, theta α ≤ 1)
    (Pbar : BlockMat d) (Pa : ι → BlockMat d)
    (hPa : ∀ α ∈ s, (1 : FullBlockMat d) ≤ toFullBlockMat (Pa α))
    (hPbar : toFullBlockMat Pbar =
      ∑ α ∈ s, theta α • toFullBlockMat (Pa α) +
        (1 - ∑ α ∈ s, theta α) • (1 : FullBlockMat d)) :
    frakH Q Pbar ≤ ∑ α ∈ s, theta α * frakH Q (Pa α) := by
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  -- each relative mean has nonnegative trace gap
  have hgap : ∀ α ∈ s, 0 ≤ blockTrace (Pa α) - 2 * (d : ℝ) := by
    intro α hα
    have hps : (toFullBlockMat (Pa α) - 1).PosSemidef := Matrix.le_iff.mp (hPa α hα)
    have htr := hps.trace_nonneg
    rw [Matrix.trace_sub, Matrix.trace_one, hcard] at htr
    exact htr
  -- the trace of the combination is the weighted combination of the trace gaps
  have htr : blockTrace Pbar - 2 * (d : ℝ) =
      ∑ α ∈ s, theta α * (blockTrace (Pa α) - 2 * (d : ℝ)) := by
    have hL : blockTrace Pbar =
        (∑ α ∈ s, theta α * blockTrace (Pa α)) +
          (1 - ∑ α ∈ s, theta α) * (2 * (d : ℝ)) := by
      show Matrix.trace (toFullBlockMat Pbar) = _
      rw [hPbar, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one,
        hcard, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.trace_smul, smul_eq_mul]
      rfl
    have hR : ∑ α ∈ s, theta α * (blockTrace (Pa α) - 2 * (d : ℝ)) =
        (∑ α ∈ s, theta α * blockTrace (Pa α)) - (∑ α ∈ s, theta α) * (2 * (d : ℝ)) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hL, hR]
    ring
  simp only [frakH]
  rw [htr]
  exact rpow_sub_one_sum_le s hQ theta (fun α => blockTrace (Pa α) - 2 * (d : ℝ)) hth hgap hm

end

end Transport
end HighContrast
end Homogenization
