import HCPoly.Entry.Analysis.SchattenSpectral
import HCPoly.Entry.Setup.MeanPenalty
import Mathlib.Tactic

/-!
# Elementary bounds for the mean penalty

This file proves the deterministic O7 sign consequence from the printed hypothesis
`I ≤ M`.  The stochastic specialization to normalized adapted means belongs to the
mean-order task once the actual source integrability and order inputs are available.
-/

open Homogenization.HighContrast (blockSub blockTrace)
namespace Homogenization.HighContrast.Analysis

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem full_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

private theorem blockMatLoewnerLE_toFull_le {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) : toFullBlockMat A ≤ toFullBlockMat B := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
  intro q
  let X : BlockVec d := ofFullBlockVec q
  have hquad :
      dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q) =
        blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) := by
    rw [← dotProduct_toFullBlockVec X
      (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X)]
    rw [toFullBlockVec_blockMatVecMul]
    simp [X]
  have hdiff :
      blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
        blockVecDot X (blockMatVecMul B X) -
          blockVecDot X (blockMatVecMul A X) := by
    simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
  have hle := hAB X
  change 0 ≤ dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q)
  rw [hquad, hdiff]
  linarith

private theorem blockIdentity_hermitian :
    (toFullBlockMat (Book.Ch02.blockIdentity d)).IsHermitian := by
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  rw [hI]
  exact Matrix.isHermitian_one

/-- If a symmetric block lies above the block identity, then its printed trace excess is
nonnegative. -/
theorem blockTrace_identity_sub_nonneg (M : BlockMat d)
    (hM : IsSymmetricBlockMat M)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M) :
    0 ≤ blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := by
  have hMH : (toFullBlockMat M).IsHermitian := (toFullBlockMat_isHermitian_iff M).2 hM
  have horder := blockMatLoewnerLE_toFull_le blockIdentity_hermitian hMH hIM
  have hdiff : (toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d))).PosSemidef := by
    rw [full_blockSub]
    exact (Matrix.le_iff).mp horder
  exact blockTrace_nonneg hdiff

/-- O7's deterministic sign: the natural-power mean penalty is nonnegative on
symmetric blocks above the identity. -/
theorem meanPenalty_nonneg (Q : ℕ) (M : BlockMat d)
    (hM : IsSymmetricBlockMat M)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M) :
    0 ≤ meanPenalty Q M := by
  have ht : 0 ≤ blockTrace (blockSub M (Book.Ch02.blockIdentity d)) :=
    blockTrace_identity_sub_nonneg M hM hIM
  have hone : 1 ≤ 1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := by
    linarith
  have hpow : 1 ≤ (1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d))) ^ Q :=
    one_le_pow₀ hone
  unfold meanPenalty
  linarith

end

end Homogenization.HighContrast.Analysis
