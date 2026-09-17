import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakEnergyDrop

/-!
# The averaged response deficit as a block quadratic form

The averaged difference of the response functional between the child cells of a triadic box and
the parent cell is the block quadratic form of the response load against the averaged
coarse-block difference.  The two cell values enter only through the hypotheses `hJ` and `hJ₀`,
so the identity is purely algebraic in the coarse blocks; identifying those values with the
response functional is a separate step.

The identity holds for every triadic index box, including the empty one.  On each child the
difference of the two quadratic forms is the quadratic form of the block defect
`blockSub (child block) (parent block)`, so the parent term cancels and the outer normalization
never needs the box to be nonempty.
-/

open Homogenization.HighContrast (blockSub)
namespace Homogenization.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The averaged response deficit is the block quadratic form of the averaged coarse-block
defect.  With `J w` the response value on the child cell `adaptedCellAtCenter q (t - n) w` and `J₀`
the response value on the parent cell `adaptedCell q t`, each written as the quadratic form of
its coarse block against the load `x`, the normalized average of the child-to-parent differences
is the quadratic form of the normalized average of the block defects
`blockSub (child block) (parent block)`. -/
theorem h6a_response_deficit_eq_blockQuadratic (q : Mat d) (t : ℤ) (n : ℕ)
    (b : CoeffField d) (x : BlockVec d)
    (J : (Fin d → ℤ) → ℝ) (J₀ : ℝ)
    (hJ : ∀ w ∈ triadicIndexBox d n,
      J w = blockVecDot x
        (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b) x))
    (hJ₀ : J₀ = blockVecDot x
      (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q t) b) x)) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, (J w - J₀)
      = blockVecDot x
          (blockMatVecMul
            (ofFullBlockMat
              (((triadicIndexBox d n).card : ℝ)⁻¹ •
                ∑ w ∈ triadicIndexBox d n,
                  toFullBlockMat
                    (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                      (coarseBlockMatrix (HighContrast.adaptedCell q t) b)))) x) := by
  let Z : Finset (Fin d → ℤ) := triadicIndexBox d n
  let C : (Fin d → ℤ) → BlockMat d := fun w =>
    coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b
  let At : BlockMat d := coarseBlockMatrix (HighContrast.adaptedCell q t) b
  let A : (Fin d → ℤ) → BlockMat d := fun w => blockSub (C w) At
  have hsum : ∑ w ∈ Z, (J w - J₀) = ∑ w ∈ Z, blockVecDot x (blockMatVecMul (A w) x) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [hJ w hw, hJ₀]
    rw [show A w = ofFullBlockMat (toFullBlockMat (C w) - toFullBlockMat At) from rfl,
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
  calc
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (J w - J₀)
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot x (blockMatVecMul (A w) x) := by
          rw [hsum]
    _ = (Z.card : ℝ)⁻¹ *
          blockVecDot x (blockMatVecMul (ofFullBlockMat (∑ w ∈ Z, toFullBlockMat (A w))) x) := by
          rw [h6a_blockVecDot_finset_sum Z A x]
    _ = blockVecDot x
          (blockMatVecMul
            (ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (A w))) x) := by
          rw [← h6a_blockVecDot_smul (Z.card : ℝ)⁻¹
            (ofFullBlockMat (∑ w ∈ Z, toFullBlockMat (A w))) x]
          simp only [toFullBlockMat_ofFullBlockMat]

end

end Homogenization.HighContrast.Multiscale
