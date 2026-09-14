/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.SchattenEntries
import HCPoly.Annealed.SchattenDefinedness
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Scalarization of the mixed norm

`l.fixed.geometry.matrix.averaging` proves a matrix estimate by proving
`4d²` scalar ones, and the passage between the two runs through the two
displays recorded here.

Downwards, the mixed norm of a random symmetric doubled block is controlled by
the `L^Q` norms of its entries,
`‖H‖_{L^Q(S_Q)} ≤ (Σ_{a,b}‖H_{ab}‖_{L^Q}²)^{1/2}`.  The proof is the printed
one: the Hilbert–Schmidt comparison `|H|_{S_Q} ≤ (Σ_{a,b}H_{ab}²)^{1/2}`
pointwise, then Minkowski's inequality in `L^{Q/2}` for the sum of the `4d²`
squares — the exponent `Q/2` is at least `1` exactly because `Q ≥ 2`.

Upwards, each entry is controlled by the mixed norm,
`‖H_{ab}‖_{L^Q} ≤ ‖H‖_{L^Q(S_Q)}`, which is the entrywise spectral bound
integrated.  The two together are what let the scalar independent-sum estimate
be applied entry by entry and reassembled.

The normalized form is the one the fixed-grid moments are written in: the
centered moment `v_r^q` is a mixed norm of a normalized block, and the
normalization of a symmetric block is symmetric with no hypothesis.
-/

namespace Homogenization
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The entry is dominated by the mixed norm -/

/-- **`‖H_{ab}‖_{L^Q} ≤ ‖H‖_{L^Q(S_Q)}`.**  The entrywise spectral bound of a
symmetric matrix holds pointwise, so it holds after taking `L^Q` norms. -/
theorem lqNorm_le_eLpNorm_schattenNorm (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 0 < Q)
    {H : CoeffSpace d → BlockMat d} (hH : ∀ a, IsSymmetricBlockMat (H a))
    (α β : BlockCoord d) :
    lqNorm P Q (fun a => toFullBlockMat (H a) α β)
      ≤ eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P := by
  simp only [lqNorm]
  refine eLpNorm_mono_real fun a => ?_
  rw [Real.norm_eq_abs]
  exact abs_toFullBlockMat_le_schattenNorm (hH a) hQ α β

/-! ## The mixed norm is dominated by the entries -/

/-- **The scalarization display of `l.fixed.geometry.matrix.averaging`**,
`‖H‖_{L^Q(S_Q)} ≤ (Σ_{a,b}‖H_{ab}‖_{L^Q}²)^{1/2}`, for a random symmetric
doubled block with measurable entries.  The Hilbert–Schmidt comparison is
applied pointwise and Minkowski's inequality is applied in `L^{Q/2}` to the
`4d²` squared entries. -/
theorem eLpNorm_schattenNorm_le (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 2 ≤ Q)
    {H : CoeffSpace d → BlockMat d} (hH : ∀ a, IsSymmetricBlockMat (H a))
    (hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (H a) α β) P) :
    eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P
      ≤ (∑ α : BlockCoord d, ∑ β : BlockCoord d,
          lqNorm P Q (fun a => toFullBlockMat (H a) α β) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
  simp only [lqNorm]
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hS0 : ∀ a : CoeffSpace d,
      (0 : ℝ) ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2 :=
    fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P
      ≤ eLpNorm (fun a =>
          (∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2) ^ (2⁻¹ : ℝ))
        (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_real fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_schattenNorm (hH a) Q)]
    exact schattenNorm_le_sum_sq_rpow (hH a) hQ
  have h2 : eLpNorm (fun a =>
        (∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2) ^ (2⁻¹ : ℝ))
        (ENNReal.ofReal Q) P
      = eLpNorm (fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2)
          (ENNReal.ofReal (Q / 2)) P ^ (2⁻¹ : ℝ) := by
    have hfun : (fun a =>
          (∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2) ^ (2⁻¹ : ℝ))
        = fun a => ‖∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2‖
            ^ (2⁻¹ : ℝ) := by
      funext a
      rw [Real.norm_eq_abs, abs_of_nonneg (hS0 a)]
    have hp : ENNReal.ofReal Q * ENNReal.ofReal (2⁻¹ : ℝ) = ENNReal.ofReal (Q / 2) := by
      rw [← ENNReal.ofReal_mul hQ0, div_eq_mul_inv]
    rw [hfun, eLpNorm_norm_rpow _ (by norm_num : (0 : ℝ) < 2⁻¹), hp]
  have hsum : (fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2)
      = ∑ i : BlockCoord d × BlockCoord d, fun a => toFullBlockMat (H a) i.1 i.2 ^ 2 := by
    funext a
    rw [Finset.sum_apply]
    exact (Fintype.sum_prod_type fun i : BlockCoord d × BlockCoord d =>
      toFullBlockMat (H a) i.1 i.2 ^ 2).symm
  have h3 : eLpNorm (fun a =>
        ∑ α : BlockCoord d, ∑ β : BlockCoord d, toFullBlockMat (H a) α β ^ 2)
        (ENNReal.ofReal (Q / 2)) P
      ≤ ∑ i : BlockCoord d × BlockCoord d,
          eLpNorm (fun a => toFullBlockMat (H a) i.1 i.2 ^ 2) (ENNReal.ofReal (Q / 2)) P := by
    rw [hsum]
    refine eLpNorm_sum_le (fun i _ => ?_) ?_
    · simpa [Pi.pow_apply] using! (hmeas i.1 i.2).pow 2
    · rw [ENNReal.one_le_ofReal]
      linarith only [hQ]
  have h4 : ∀ i : BlockCoord d × BlockCoord d,
      eLpNorm (fun a => toFullBlockMat (H a) i.1 i.2 ^ 2) (ENNReal.ofReal (Q / 2)) P
        = eLpNorm (fun a => toFullBlockMat (H a) i.1 i.2) (ENNReal.ofReal Q) P ^ (2 : ℝ) := by
    intro i
    have hfun : (fun a => toFullBlockMat (H a) i.1 i.2 ^ 2)
        = fun a => ‖toFullBlockMat (H a) i.1 i.2‖ ^ (2 : ℝ) := by
      funext a
      rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hp : ENNReal.ofReal (Q / 2) * ENNReal.ofReal (2 : ℝ) = ENNReal.ofReal Q := by
      rw [← ENNReal.ofReal_mul (by linarith only [hQ] : (0 : ℝ) ≤ Q / 2)]
      congr 1
      ring
    rw [hfun, eLpNorm_norm_rpow _ (by norm_num : (0 : ℝ) < 2), hp]
  refine le_trans h1 (le_trans (le_of_eq h2) ?_)
  refine ENNReal.rpow_le_rpow (le_trans h3 ?_) (by norm_num)
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun α _ =>
    Finset.sum_le_sum fun β _ => le_of_eq (h4 (α, β))

/-! ## The normalized form -/

/-- **The scalarization display in the normalized carrier of the fixed-grid
estimates.**  The mixed norm `‖F^{-1/2}·F^{-1/2}‖_{L^Q(S_Q)}` of a random
symmetric block is bounded by the `L^Q` norms of the entries of the normalized
block; the normalization of a symmetric block is symmetric whatever the
normalizing block, so no extra symmetry is assumed of it. -/
theorem lqSchattenSize_le (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 2 ≤ Q)
    {A : CoeffSpace d → BlockMat d} (F : BlockMat d) (hA : ∀ a, IsSymmetricBlockMat (A a))
    (hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (normalizedBlock (A a) F) α β) P) :
    lqSchattenSize P Q A F
      ≤ (∑ α : BlockCoord d, ∑ β : BlockCoord d,
          lqNorm P Q (fun a => toFullBlockMat (normalizedBlock (A a) F) α β) ^ (2 : ℝ))
        ^ (2⁻¹ : ℝ) :=
  eLpNorm_schattenNorm_le P hQ
    (fun a => isSymmetricBlockMat_normalizedBlock (F := F) (hA a)) hmeas

end

end Recurrence
end HighContrast
end Homogenization
