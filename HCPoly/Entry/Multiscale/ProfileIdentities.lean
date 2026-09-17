import HCPoly.Entry.Geometry.LoewnerCongruence
import HCPoly.Entry.Setup.Profile

/-!
# Diagonal profile identities

This file contains only the deterministic finite-sum and normalization algebra needed at
the diagonal `m = n`.  The positivity assumption is kept exactly where the total
normalization needs it.
-/

open Homogenization.HighContrast (CoeffSpace adaptedMean blockSub blockTrace matSqrt matSqrt_spec
  normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- The inverse square root is positive definite on every finite real matrix carrier. -/
theorem matSqrt_inv_posDef_full {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : Matrix ι ι ℝ} (hm : m.PosDef) : (matSqrt m⁻¹).PosDef := by
  rw [matSqrt_eq_cfc_sqrt hm.inv.posSemidef]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt m⁻¹ hm.inv.isStrictlyPositive)

/-- Inverse square-root congruence normalizes a positive definite matrix to one. -/
theorem matSqrt_inv_mul_self_mul_matSqrt_inv_full
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Matrix ι ι ℝ} (hm : m.PosDef) :
    matSqrt m⁻¹ * m * matSqrt m⁻¹ = 1 := by
  let S : Matrix ι ι ℝ := matSqrt m⁻¹
  have hSS : S * S = m⁻¹ := (matSqrt_spec hm.inv.posSemidef).2
  have hmDet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp hm.isUnit
  have hright : S * (S * m) = 1 := by
    rw [← mul_assoc, hSS, Matrix.nonsing_inv_mul m hmDet]
  have hSinv : S⁻¹ = S * m := Matrix.inv_eq_right_inv hright
  have hSDet : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).mp (matSqrt_inv_posDef_full hm).isUnit
  calc
    S * m * S = S⁻¹ * S := by rw [hSinv]
    _ = 1 := Matrix.nonsing_inv_mul S hSDet

private theorem ofFullBlockMat_one_eq_blockIdentity {d : ℕ} :
    ofFullBlockMat (1 : FullBlockMat d) = Book.Ch02.blockIdentity d := by
  rw [← ofFullBlockMat_toFullBlockMat (Book.Ch02.blockIdentity d)]
  congr
  funext α β
  cases α <;> cases β <;>
    simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]

private theorem blockTrace_blockSub_identity_self {d : ℕ} :
    blockTrace (blockSub (Book.Ch02.blockIdentity d) (Book.Ch02.blockIdentity d)) = 0 := by
  unfold blockTrace
  have hzero :
      toFullBlockMat (blockSub (Book.Ch02.blockIdentity d) (Book.Ch02.blockIdentity d)) =
        (0 : FullBlockMat d) := by
    funext α β
    cases α <;> cases β <;> simp [blockSub, toFullBlockMat]
  rw [hzero, Matrix.trace_zero]

/-- Normalizing a positive definite block by itself gives the doubled identity. -/
theorem normalizedBlock_self_of_posDef
    {d : ℕ} (F : BlockMat d) (hF : (toFullBlockMat F).PosDef) :
    normalizedBlock F F = Book.Ch02.blockIdentity d := by
  unfold normalizedBlock
  rw [matSqrt_inv_mul_self_mul_matSqrt_inv_full hF]
  exact ofFullBlockMat_one_eq_blockIdentity

/-- The mean penalty of the identity is zero, for every natural moment including `0`. -/
theorem meanPenalty_identity
    {d : ℕ} (Q : ℕ) :
    meanPenalty Q (Book.Ch02.blockIdentity d) = 0 := by
  simp [meanPenalty, blockTrace_blockSub_identity_self]

/-- At the diagonal, the profile is exactly the printed prefactor times the history. -/
theorem profile_self_eq_factor_mul_history
    {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (n : ℤ) :
    profile P γ q jStar n n =
    (1 + meanPenalty (bigQ d γ) (normalizedMean P q n n)) * history P γ q jStar n := by
  unfold profile meanHistory
  simp

/-- With a positive terminal mean, the diagonal normalized mean is the identity. -/
theorem profile_self_of_posDef
    {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (n : ℤ)
    (hF : (toFullBlockMat (adaptedMean P q n)).PosDef) :
    profile P γ q jStar n n = history P γ q jStar n := by
  rw [profile_self_eq_factor_mul_history]
  simp [normalizedMean, normalizedBlock_self_of_posDef (adaptedMean P q n) hF,
    meanPenalty_identity]

end

end Homogenization.HighContrast.Multiscale
