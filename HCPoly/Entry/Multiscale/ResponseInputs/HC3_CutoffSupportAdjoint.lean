import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportChainRule
import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic

/-!
# The two slots of the pulled-back pairing

A linear change of variables `x = q y` transports a cutoff `φ` to `y ↦ φ (q y)`.  The gradient
of the transported cutoff is the transpose `qᵀ` applied to the gradient of `φ` at `q y`; this is
the chain rule recorded in `fderiv_comp_matVecMul_basisVec`.  The three declarations below collect
the linear-algebraic consequences needed to distribute the grid `q` between the two slots of the
Euclidean pairing without cost:  when one slot of the pairing is pulled back by `q⁻¹`, the other
acquires `qᵀ`, and the adjointness of `qᵀ` cancels the two against each other.  This is the
change-of-variables step of the cutoff argument in the response estimate
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)).
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- For an invertible matrix `q`, the inverse `q⁻¹` cancels `q` under `matVecMul`: applying `q`
to `q⁻¹ v` returns `v`. -/
theorem matVecMul_matVecMul_inv_cancel {d : ℕ} {q : Mat d} (hq : IsUnit q) (v : Vec d) :
    matVecMul q (matVecMul q⁻¹ v) = v := by
  have hqdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det (A := q)).mp hq
  rw [matVecMul_mul, Matrix.mul_nonsing_inv q hqdet]
  funext i
  simp [matVecMul, Matrix.one_apply]

/-- The gradient of the pulled-back cutoff `y ↦ φ (q y)` is `qᵀ` applied to the gradient of `φ`
at `q y`, in the coordinatewise gradient convention of the project: the gradient field of the
composition is the transpose of the grid applied to the pulled-back gradient field. -/
theorem scalarCutoffGradientField_comp_eq {d : ℕ} (q : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : Vec d) :
    scalarCutoffGradientField (fun z : Vec d => φ (matVecMul q z)) y
      = matVecMul (matTranspose q) (scalarCutoffGradientField φ (matVecMul q y)) := by
  funext i
  exact congrFun (fderiv_comp_matVecMul_basisVec q hφ y) i

/-- The Euclidean pairing is preserved when the first slot acquires `q⁻¹` and the second the
transpose of the grid: for an invertible `q`,
`⟪q⁻¹ v, ∇(φ ∘ q)(y)⟫ = ⟪v, ∇φ(q y)⟫`. -/
theorem vecDot_pullback_slots {d : ℕ} {q : Mat d} (hq : IsUnit q) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : Vec d) (y : Vec d) :
    vecDot (matVecMul q⁻¹ v)
        (scalarCutoffGradientField (fun z : Vec d => φ (matVecMul q z)) y)
      = vecDot v (scalarCutoffGradientField φ (matVecMul q y)) := by
  rw [scalarCutoffGradientField_comp_eq q hφ y]
  calc
    vecDot (matVecMul q⁻¹ v)
        (matVecMul (matTranspose q) (scalarCutoffGradientField φ (matVecMul q y)))
        = vecDot (matVecMul (matTranspose q) (scalarCutoffGradientField φ (matVecMul q y)))
            (matVecMul q⁻¹ v) := vecDot_comm _ _
    _ = vecDot (scalarCutoffGradientField φ (matVecMul q y))
            (matVecMul q (matVecMul q⁻¹ v)) :=
          vecDot_matVecMul_transpose q _ _
    _ = vecDot (scalarCutoffGradientField φ (matVecMul q y)) v := by
          rw [matVecMul_matVecMul_inv_cancel hq v]
    _ = vecDot v (scalarCutoffGradientField φ (matVecMul q y)) := vecDot_comm _ _

end

end Homogenization.HighContrast.Multiscale
