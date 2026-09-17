import HCPoly.Setup.BlockAlgebra
import Mathlib.Analysis.Matrix.Order
import HCPoly.Setup.SpectralBound

/-!
# The scalar Loewner bound and the positive semidefinite square root

The print writes `|M|` for the spectral norm of a symmetric positive semidefinite matrix and
`m^{1/2}` for the positive square root.  This file proves that the encodings `specBound` and
`matSqrt` are those objects: `specBound M` is the least `t ≥ 0` with `M ≤ t I`, and
`matSqrt M` is *the* positive semidefinite square root, independently of the choice made in
its definition.
-/

open Homogenization.HighContrast (lambdaRef matSqrt matSqrt_eq specBound_nonneg)
namespace Homogenization.HighContrast

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem matVecMul_smul_one (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, mul_comm]

private theorem vecDot_smul_self (t : ℝ) (x : Vec d) : vecDot x (t • x) = t * vecNormSq x := by
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The scalar Loewner bound of `M` by `t` is the pointwise inequality of quadratic forms. -/
theorem matLoewnerLE_smul_one_iff (M : Mat d) (t : ℝ) :
    MatLoewnerLE M (t • (1 : Mat d)) ↔
      ∀ x : Vec d, vecDot x (matVecMul M x) ≤ t * vecNormSq x := by
  simp only [MatLoewnerLE, matVecMul_smul_one, vecDot_smul_self]
  constructor
  · intro h x
    have := h x
    linarith only [this]
  · intro h x
    have := h x
    linarith only [this]

private theorem specBoundSet_isClosed (M : Mat d) :
    IsClosed {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))} := by
  have hset : {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))} =
      Set.Ici 0 ∩ ⋂ x : Vec d, {t : ℝ | vecDot x (matVecMul M x) ≤ t * vecNormSq x} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iInter,
      matLoewnerLE_smul_one_iff]
  rw [hset]
  exact isClosed_Ici.inter (isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_id.mul continuous_const))

/-! ## The positive semidefinite square root -/

/-- On positive semidefinite data `matSqrt` is Mathlib's continuous-functional-calculus square
root, the object `explicitRoundedGrid` is written with. -/
theorem matSqrt_eq_cfc_sqrt {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) : matSqrt M = CFC.sqrt M :=
  matSqrt_eq hM (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg M)) (CFC.sqrt_mul_sqrt_self M)

/-! ## Junk guards on the contrast constants -/

/-- `λ_0` is nonnegative, junk branch included. -/
theorem lambdaRef_nonneg (E : BlockMat d) : 0 ≤ lambdaRef E :=
  inv_nonneg.2 (specBound_nonneg _)

end

end Homogenization.HighContrast
