import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentLoewner

/-!
# The normalized block commutes with finite averages

`normalizedBlock H F = F^{-1/2} H F^{-1/2}` is linear in its first argument, so the flat
average of the normalized cell defects is the normalized block of the flat average of the
defects.  This file records that identity — in scalar, finite-set and recent-carrier form —
and then reads the resulting quadratic bound off the already proved Loewner comparison
`h6a_quadratic_le_norm_normalizedBlock`.

This is the algebraic half of the difference-energy step of the cell-average lemma: the
normalizing congruence is applied to the averaged defect rather than to each defect
separately.  Nothing here assumes a sign or a symmetry of the defect block, only that the
normalizing block is positive definite at the quadratic-bound consumer.
-/

open Homogenization.HighContrast (blockSub normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open scoped Matrix MatrixOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The normalization distributes over a finite weighted average: conjugating each summand by
the fixed root and then averaging is the same as conjugating the averaged defect.  The scalar
`c` is applied only to the output, so the identity holds for every finite set `Z`, including
the empty set and `c = 0`. -/
theorem h6a_normalizedBlock_finset_average {iota : Type*} (Z : Finset iota)
    (D : iota → BlockMat d) (F : BlockMat d) (c : ℝ) :
    c • ∑ w ∈ Z, toFullBlockMat (normalizedBlock (D w) F)
      = toFullBlockMat
          (normalizedBlock (ofFullBlockMat (c • ∑ w ∈ Z, toFullBlockMat (D w))) F) := by
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]

/-- The recent averaged normalized defect of `weakAverageDefect` is the normalized block of
the flat average of the recent cell defects.  This is
`h6a_normalizedBlock_finset_average` at the triadic index box, the weight
`(card)⁻¹` and the recent coarse-block difference. -/
theorem h6a_weakAverageDefect_eq_normalizedBlock (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d)
    (b : CoeffField d) :
    weakAverageDefect q t n E b
      = normalizedBlock
          (ofFullBlockMat
            (((triadicIndexBox d n).card : ℝ)⁻¹ •
              ∑ w ∈ triadicIndexBox d n,
                toFullBlockMat
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b))))
          E := by
  unfold weakAverageDefect
  rw [h6a_normalizedBlock_finset_average]
  rw [ofFullBlockMat_toFullBlockMat]

/-- The quadratic form of the flat recent average of the cell defects, read against a positive
definite metric `E`, is controlled by the operator norm of its `E`-normalized block times the
`E`-quadratic form of the test vector.  This is the difference-energy bound of the cell-average
lemma, obtained from `h6a_quadratic_le_norm_normalizedBlock` by identifying the normalized
block of the averaged defect with `weakAverageDefect`. -/
theorem h6a_average_defect_quadratic_le (q : Mat d) (t : ℤ) (n : ℕ) {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (b : CoeffField d) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat
            (((triadicIndexBox d n).card : ℝ)⁻¹ •
              ∑ w ∈ triadicIndexBox d n,
                toFullBlockMat
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b))))
          X)
      ≤ ‖toFullBlockMat (weakAverageDefect q t n E b)‖ * blockVecDot X (blockMatVecMul E X) := by
  have h := h6a_quadratic_le_norm_normalizedBlock E
    (ofFullBlockMat
      (((triadicIndexBox d n).card : ℝ)⁻¹ •
        ∑ w ∈ triadicIndexBox d n,
          toFullBlockMat
            (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
              (coarseBlockMatrix (HighContrast.adaptedCell q t) b))))
    hE X
  rw [← h6a_weakAverageDefect_eq_normalizedBlock q t n E b] at h
  exact h

end

end Homogenization.HighContrast.Multiscale
