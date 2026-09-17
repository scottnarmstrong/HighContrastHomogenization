import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentDecomp

/-!
# The recent-scale decomposition with box-restricted integrability

The recent-scale decomposition compares the normalized root-mean-square, over the depth-`n`
triadic cells, of the transported and recentred parent cell averages with the corresponding child
average plus the average of the parent-minus-child difference.  Its conclusion sums only over the
cells indexed by `triadicIndexBox d n`, and its window sum only over `n ≤ H`, so the
integrability of the fields is needed only on those cells: a cell index outside the box is never
averaged.

This module restates the decomposition with that restricted hypothesis, which is the form the
optimizer field can actually supply, since the parent field is `L²` only on the adapted region
`U`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The recent-scale decomposition at one depth, with box-restricted integrability.**  At depth
`n`, the head term of the actual family — the normalized root-mean-square over the triadic cells
of the transported, recentred parent cell averages — is at most the corresponding child term plus
the average-defect term, assuming the componentwise integrability of the parent and child fields
only on the triadic cells indexed by `triadicIndexBox d n`. -/
theorem h6a_recent_scale_decomposition_box_le (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (Xu : Vec d → BlockVec d) (Xv : (Fin d → ℤ) → Vec d → BlockVec d) (c : BlockVec d)
    (h1u : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2u : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h1v : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv w x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2v : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv w x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c)))
      ≤ Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv w) - c))
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv w) - c)))
        + Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (fun x => Xu x - Xv w x)))
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (fun x => Xu x - Xv w x)))) := by
  classical
  set C : (Fin d → ℤ) → BlockVec d := fun w =>
    blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv w) - c) with hC
  set D : (Fin d → ℤ) → BlockVec d := fun w =>
    blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
      (fun x => Xu x - Xv w x)) with hD
  have hsplit : ∀ w ∈ triadicIndexBox d n,
      blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c) = C w + D w :=
    fun w hw => h6a_recent_cell_split R Xu (Xv w) c
      (h1u w hw) (h2u w hw) (h1v w hw) (h2v w hw)
  have hrw : ∑ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
        (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
      = ∑ w ∈ triadicIndexBox d n, blockVecDot (C w + D w) (C w + D w) :=
    Finset.sum_congr rfl fun w hw => congrArg₂ blockVecDot (hsplit w hw) (hsplit w hw)
  rw [hrw]
  exact h6a_normalized_blockL2_add_le (triadicIndexBox d n) C D

omit [NeZero d] in
/-- **The recent-scale decomposition summed over the window, with box-restricted integrability.**
The depth-`n` decomposition summed over `n ≤ H` against the `3^{-n/2}` weights, assuming the
componentwise integrability of the parent and child fields only on the triadic cells indexed by
`triadicIndexBox d n` for each `n` in the window. -/
theorem h6a_recentHead_scale_decomposition_box_le (q : Mat d) (t : ℤ) (H : ℕ) (R : BlockMat d)
    (Xu : Vec d → BlockVec d) (Xv : ℕ → (Fin d → ℤ) → Vec d → BlockVec d) (c : BlockVec d)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h1v : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv n w x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2v : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv n w x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    ∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) *
          Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c)))
      ≤ ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul R
                      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv n w) - c))
                    (blockMatVecMul R
                      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv n w) - c)))
              + Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                  ∑ w ∈ triadicIndexBox d n,
                    blockVecDot
                      (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                        (fun x => Xu x - Xv n w x)))
                      (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                        (fun x => Xu x - Xv n w x))))) := by
  refine Finset.sum_le_sum fun n hn => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
  exact h6a_recent_scale_decomposition_box_le q t n R Xu (Xv n) c
    (h1u n hn) (h2u n hn) (h1v n hn) (h2v n hn)

end

end Homogenization.HighContrast.Multiscale
