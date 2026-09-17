import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakNormAverage

namespace Homogenization.HighContrast.Multiscale

open scoped Matrix MatrixOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The doubled quadratic form of a finite sum of blocks is the sum of the quadratic forms: the
pairing `(X, Y) ↦ X · A Y` is linear in the flat representative `A`, and `ofFullBlockMat`
respects finite sums.  The identity holds for every finite index set, including the empty one. -/
theorem h6a_blockVecDot_finset_sum {iota : Type*} (Z : Finset iota) (D : iota → BlockMat d)
    (x : BlockVec d) :
    ∑ w ∈ Z, blockVecDot x (blockMatVecMul (D w) x)
      = blockVecDot x
          (blockMatVecMul (ofFullBlockMat (∑ w ∈ Z, toFullBlockMat (D w))) x) := by
  have h : ∀ A : BlockMat d,
      blockVecDot x (blockMatVecMul A x)
        = toFullBlockVec x ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec x) := by
    intro A
    rw [← dotProduct_toFullBlockVec x (blockMatVecMul A x), toFullBlockVec_blockMatVecMul]
  simp only [h, toFullBlockMat_ofFullBlockMat, Matrix.sum_mulVec, dotProduct_sum]

/-- The doubled quadratic form is homogeneous in the flat representative `A`: dilating a block by
a scalar dilates the quadratic form by the same scalar. -/
theorem h6a_blockVecDot_smul (c : ℝ) (D : BlockMat d) (x : BlockVec d) :
    blockVecDot x (blockMatVecMul (ofFullBlockMat (c • toFullBlockMat D)) x)
      = c * blockVecDot x (blockMatVecMul D x) := by
  have h : ∀ A : BlockMat d,
      blockVecDot x (blockMatVecMul A x)
        = toFullBlockVec x ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec x) := by
    intro A
    rw [← dotProduct_toFullBlockVec x (blockMatVecMul A x), toFullBlockVec_blockMatVecMul]
  simp only [h, toFullBlockMat_ofFullBlockMat, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end

end Homogenization.HighContrast.Multiscale
