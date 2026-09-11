/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridExhaustion

/-!
# Algebra for reverse-hybrid rows

Finite positive matrix sums and the split at the alignment scale put the
hybrid exhaustion into the quadratic form used by the pathwise comparison.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A finite sum of positive semidefinite full block matrices is positive
semidefinite. -/
theorem hybrid_posSemidef_finset_sum {ι : Type*} {s : Finset ι}
    {A : ι → FullBlockMat d} (h : ∀ i ∈ s, (A i).PosSemidef) :
    (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- A uniform bound on all rows below the alignment scale can be appended to
the finite rows at and above that scale. -/
theorem hybrid_sum_Icc_le_add_of_below {jStar n : ℤ} (hjn : jStar ≤ n)
    {row : ℤ → ℝ} {G : ℝ} (hrow0 : ∀ r, 0 ≤ row r) (hG0 : 0 ≤ G)
    (hbelow : ∀ J : ℤ, ∑ r ∈ Finset.Ico J jStar, row r ≤ G) (J : ℤ) :
    ∑ r ∈ Finset.Icc J n, row r ≤
      (∑ r ∈ Finset.Icc jStar n, row r) + G := by
  rcases le_or_gt jStar J with hle | hlt
  · have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := row) (Finset.Icc_subset_Icc hle (le_refl n))
      (fun i _ _ => hrow0 i)
    exact hmono.trans (le_add_of_nonneg_right hG0)
  · have hdisj : Disjoint (Finset.Ico J jStar) (Finset.Icc jStar n) := by
      refine Finset.disjoint_left.mpr fun i hi hi' => ?_
      rw [Finset.mem_Ico] at hi
      rw [Finset.mem_Icc] at hi'
      omega
    have hsplit : Finset.Icc J n =
        Finset.Ico J jStar ∪ Finset.Icc jStar n := by
      show Finset.Ico J (n + 1) =
        Finset.Ico J jStar ∪ Finset.Ico jStar (n + 1)
      exact (Finset.Ico_union_Ico_eq_Ico hlt.le (by omega)).symm
    rw [hsplit, Finset.sum_union hdisj]
    simpa only [add_comm] using
      add_le_add_right (hbelow J) (∑ r ∈ Finset.Icc jStar n, row r)

/-- The half quadratic form of the full hybrid majorant separates into its
packed row, selected old-grid rows, and scalar remainder. -/
theorem blockQuadratic_hybridMajorant (X : BlockVec d)
    (Zp : Finset (Fin d → ℤ)) (Z : ℤ → Finset (Fin d → ℤ))
    (R : Finset ℤ) (wp : (Fin d → ℤ) → ℝ)
    (wr : ℤ → (Fin d → ℤ) → ℝ)
    (Ap : (Fin d → ℤ) → BlockMat d)
    (Ar : ℤ → (Fin d → ℤ) → BlockMat d) (c : ℝ) (E : BlockMat d) :
    1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat
        ((∑ w ∈ Zp, wp w • toFullBlockMat (Ap w)) +
          (∑ r ∈ R, ∑ w ∈ Z r, wr r w • toFullBlockMat (Ar r w)) +
          c • toFullBlockMat E)) X) =
      (∑ w ∈ Zp, wp w *
          (1 / 2 * blockVecDot X (blockMatVecMul (Ap w) X))) +
        (∑ r ∈ R, ∑ w ∈ Z r, wr r w *
          (1 / 2 * blockVecDot X (blockMatVecMul (Ar r w) X))) +
        c * (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
  rw [blockVecDot_blockMatVecMul_eq_dotProduct,
    toFullBlockMat_ofFullBlockMat, Matrix.add_mulVec, dotProduct_add,
    Matrix.add_mulVec, dotProduct_add, mul_add, mul_add]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · rw [Matrix.sum_mulVec, dotProduct_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          blockVecDot_blockMatVecMul_eq_dotProduct]
        ring
    · rw [Matrix.sum_mulVec, dotProduct_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Matrix.sum_mulVec, dotProduct_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          blockVecDot_blockMatVecMul_eq_dotProduct]
        ring
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      blockVecDot_blockMatVecMul_eq_dotProduct]
    ring

end

end Bridge
end HighContrast
end Homogenization
