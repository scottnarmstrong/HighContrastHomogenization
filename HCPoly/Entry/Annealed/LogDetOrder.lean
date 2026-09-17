import HCPoly.Entry.Annealed.MeanOrder
import HCPoly.Entry.Annealed.Normalization
import HCPoly.Entry.Analysis.MeanPenaltyBounds
import HCPoly.Entry.Multiscale.DriftAdvance

/-!
# Ordered means and the coefficient-one determinant loss

`p.fixed.geometry.parent.child.recurrence`. Full doubled matrices are normalized without a
commutation assumption. The determinant is the full 2d determinant, with no root.
-/

open Homogenization.HighContrast (CoeffSpace blockLogDet blockSub blockTrace matSqrt
  normalizedBlock)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory Geometry
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- Full matrix order and the CG quadratic block order agree on symmetric blocks. -/
theorem fullBlock_le_iff {d : ℕ} {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian) :
    toFullBlockMat A ≤ toFullBlockMat B ↔ BlockMatLoewnerLE A B := by
  constructor
  · intro h X
    have hn := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (toFullBlockVec X)
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hn
    have heA := dotProduct_toFullBlockVec X (blockMatVecMul A X)
    have heB := dotProduct_toFullBlockVec X (blockMatVecMul B X)
    rw [toFullBlockVec_blockMatVecMul] at heA heB
    rw [heA, heB] at hn
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hn) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro h
    apply Matrix.le_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
    intro x
    have hx := h (ofFullBlockVec x)
    simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec] at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]

/-- The operator norm above identity is bounded by one plus the full trace excess. -/
theorem blockOpNorm_le_one_add_trace {d : ℕ} (M : BlockMat d)
    (hM : (toFullBlockMat M).IsHermitian)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M) :
    blockOpNorm M ≤ 1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := by
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hIP : (1 : FullBlockMat d) ≤ toFullBlockMat M := by
    rw [← hI]
    exact (fullBlock_le_iff (by rw [hI]; exact Matrix.isHermitian_one) hM).2 hIM
  have hsub : toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d)) = toFullBlockMat M - 1 := by
    rw [← hI]
    ext α β
    cases α <;> cases β <;> rfl
  have hp : (toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d))).PosSemidef := by
    rw [hsub]
    exact Matrix.le_iff.mp hIP
  have hnorm : ‖toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d))‖ ≤
      blockTrace (blockSub M (Book.Ch02.blockIdentity d)) :=
    (Analysis.blockOpNorm_le_absSchattenNorm hp.isHermitian le_rfl).trans
      (Analysis.absSchattenNorm_le_blockTrace hp le_rfl)
  calc
    blockOpNorm M = ‖(toFullBlockMat M - 1) + 1‖ := by simp only [sub_add_cancel, blockOpNorm]
    _ ≤ ‖toFullBlockMat M - 1‖ + ‖(1 : FullBlockMat d)‖ := norm_add_le _ _
    _ ≤ blockTrace (blockSub M (Book.Ch02.blockIdentity d)) + 1 := by
      rw [← hsub]
      apply add_le_add hnorm
      rcases isEmpty_or_nonempty (BlockCoord d) with hi | hi
      · let := hi
        have he : (1 : FullBlockMat d) = 0 := Subsingleton.elim _ _
        rw [he, norm_zero]
        norm_num
      · let := hi
        simp
    _ = _ := add_comm _ _

/-- The full determinant controls normalized order, loss, operator norm, trace and O7. -/
theorem normalizedBlock_order_consequences {d : ℕ} (Q : ℕ) (F G : BlockMat d)
    (hF : (toFullBlockMat F).PosDef) (hG : (toFullBlockMat G).PosDef)
    (hGF : BlockMatLoewnerLE G F) :
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (normalizedBlock F G) ∧
      0 ≤ blockLogDet F - blockLogDet G ∧
      (toFullBlockMat (normalizedBlock F G)).det = Real.exp (blockLogDet F - blockLogDet G) ∧
      blockOpNorm (normalizedBlock F G) ≤ Real.exp (blockLogDet F - blockLogDet G) ∧
      blockTrace (blockSub (normalizedBlock F G) (Book.Ch02.blockIdentity d)) ≤
        Real.exp (blockLogDet F - blockLogDet G) - 1 ∧
      0 ≤ meanPenalty Q (normalizedBlock F G) := by
  let M := normalizedBlock F G
  have hS := Multiscale.matSqrt_inv_posDef_full hG
  have hp : (toFullBlockMat M).PosSemidef := by
    simpa only [M, normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
      hF.posSemidef.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat G)⁻¹)
  have hIP : (1 : FullBlockMat d) ≤ toFullBlockMat M := by
    simpa only [M, normalizedBlock, toFullBlockMat_ofFullBlockMat] using
      Multiscale.one_le_normalized hG ((fullBlock_le_iff hG.isHermitian hF.isHermitian).2 hGF)
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M := by
    apply (fullBlock_le_iff (by rw [hI]; exact Matrix.isHermitian_one) hp.isHermitian).1
    simpa only [hI] using hIP
  have hsym : IsSymmetricBlockMat M := (Analysis.toFullBlockMat_isHermitian_iff M).1 hp.isHermitian
  have htrace := Multiscale.normalizedMean_trace_sub_identity_le F G hF hG hGF
  have hnonneg := Analysis.blockTrace_identity_sub_nonneg M hsym hIM
  have hloss : 0 ≤ blockLogDet F - blockLogDet G := by
    apply Real.one_le_exp_iff.mp
    linarith only [htrace, hnonneg]
  have hdet := Multiscale.det_normalizedBlock_eq_exp F G hF hG
  have hnorm : blockOpNorm M ≤ Real.exp (blockLogDet F - blockLogDet G) := by
    have hb := blockOpNorm_le_one_add_trace M hp.isHermitian hIM
    linarith only [hb, htrace]
  exact ⟨hIM, hloss, hdet, hnorm, htrace, Analysis.meanPenalty_nonneg Q M hsym hIM⟩

/-- The complete ordered-mean consequences with all stochastic guards discharged. -/
theorem adaptedMean_order_consequences (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    let q := explicitRoundedGrid jStar m
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (normalizedMean P q j k) ∧
      0 ≤ logDetLoss P q j k ∧
      (toFullBlockMat (normalizedMean P q j k)).det = Real.exp (logDetLoss P q j k) ∧
      blockOpNorm (normalizedMean P q j k) ≤ Real.exp (logDetLoss P q j k) ∧
      blockTrace (blockSub (normalizedMean P q j k) (Book.Ch02.blockIdentity d)) ≤
        Real.exp (logDetLoss P q j k) - 1 ∧
      0 ≤ meanPenalty (bigQ d γ) (normalizedMean P q j k) := by
  exact normalizedBlock_order_consequences (bigQ d γ) _ _
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j)
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm k)
    (adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j k hj hjk)

/-- O2 for every pair of admissible generations in the actual rounded grid. -/
theorem logDetLoss_nonneg (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    0 ≤ logDetLoss P (explicitRoundedGrid jStar m) j k :=
  (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j k hj hjk).2.1

end

end Homogenization.HighContrast.Annealed
