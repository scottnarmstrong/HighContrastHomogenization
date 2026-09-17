import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import Homogenization.Ambient.CoefficientFieldHilbert

/-!
# The gradient of a pulled-back cutoff

The linear change of variables `x = q y` transports a cutoff `φ` from the adapted cell to the
reference cube as `y ↦ φ (q y)`.  Its gradient is `qᵀ` applied to the gradient of `φ` at `q y`.
The two declarations below record the adjoint identity for the Euclidean pairing and the chain
rule in the coordinatewise gradient convention of the project.  This is the linear-algebraic step
of the cutoff argument in the response estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1,
(A.4)).
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The adjoint identity for the Euclidean pairing: the transpose `qᵀ` is the adjoint of `q` with
respect to `vecDot`, i.e. `⟪qᵀ v, z⟫ = ⟪v, q z⟫`. -/
theorem vecDot_matVecMul_transpose {d : ℕ} (q : Mat d) (v z : Vec d) :
    vecDot (matVecMul (matTranspose q) v) z = vecDot v (matVecMul q z) := by
  simp only [vecDot, matVecMul, matTranspose, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The `k`-th coordinate of `∑ j, c j • basisVec j` is `c k`. -/
private theorem sum_smul_basisVec_apply {d : ℕ} (c : Fin d → ℝ) (k : Fin d) :
    (∑ j : Fin d, c j • basisVec j) k = c k := by
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp only [Pi.smul_apply, basisVec_apply, smul_eq_mul, if_true, mul_one]
  · intro j _ hj
    have hkj : k ≠ j := fun h => hj h.symm
    simp only [Pi.smul_apply, basisVec_apply, smul_eq_mul, if_neg hkj, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The `i`-th column of `q` is the image of the `i`-th basis vector under `matVecMul q`, written
as the linear combination `∑ j, q j i • basisVec j` of basis vectors. -/
private theorem matVecMul_basisVec_eq_sum {d : ℕ} (q : Mat d) (i : Fin d) :
    matVecMul q (basisVec i) = ∑ j : Fin d, q j i • basisVec j := by
  funext k
  rw [sum_smul_basisVec_apply (fun j : Fin d => q j i) k]
  simp only [matVecMul, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · simp only [if_true, mul_one]
  · intro j _ hj
    simp only [if_neg hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The chain rule for the linear change of variables `x = q y`, in the coordinatewise gradient
convention of the project: the gradient of the pulled-back function `y ↦ φ (q y)` is `qᵀ` applied
to the gradient of `φ` at `q y`, i.e.
`(fun j => (fderiv ℝ (φ ∘ q)) y (basisVec j)) = matVecMul qᵀ (fun j => (fderiv ℝ φ (q y)) (basisVec j))`.
-/
theorem fderiv_comp_matVecMul_basisVec {d : ℕ} (q : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : Vec d) :
    (fun j => (fderiv ℝ (fun z : Vec d => φ (matVecMul q z)) y) (basisVec j))
      = matVecMul (matTranspose q) (fun j => (fderiv ℝ φ (matVecMul q y)) (basisVec j)) := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hderiv : HasFDerivAt (fun z : Vec d => φ (matVecMul q z))
      ((fderiv ℝ φ (matVecMul q y)).comp (matContinuousLinearMap q)) y :=
    (hdiff (matVecMul q y)).hasFDerivAt.comp y ((matContinuousLinearMap q).hasFDerivAt)
  have hfd : fderiv ℝ (fun z : Vec d => φ (matVecMul q z)) y
      = (fderiv ℝ φ (matVecMul q y)).comp (matContinuousLinearMap q) := hderiv.fderiv
  funext i
  rw [hfd, ContinuousLinearMap.comp_apply, matContinuousLinearMap_apply,
    matVecMul_basisVec_eq_sum, map_sum]
  change (∑ j : Fin d, (fderiv ℝ φ (matVecMul q y)) (q j i • basisVec j))
      = ∑ j : Fin d, (matTranspose q) i j *
          (fderiv ℝ φ (matVecMul q y)) (basisVec j)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  simp only [matTranspose, Matrix.transpose_apply]

end

end Homogenization.HighContrast.Multiscale
