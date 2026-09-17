import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic
import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.NormalizedAndGradient

/-!
# The pulled-back cutoff gradient as an admissible weight field

For a cutoff `φ` and a matrix `qq`, the pulled-back cutoff is `ψ(y) = φ (qq · y)`.  Its gradient
field `scalarCutoffGradientField ψ` is the weight field `ξ` consumed by the negative-Besov duality
bound for the product term of the cutoff estimate (`e.response.cutoff.estimate`), which needs three
facts about `ξ`: it is smooth coordinatewise, each coordinate field has derivative bounded by the
second-derivative bound carried by the cutoff class, and `ξ` is bounded by the Lipschitz constant
of the pulled-back cutoff.  The three declarations below record exactly those facts.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The continuous linear map underlying the pullback `y ↦ qq · y`, used to move between the
pulled-back cutoff and `φ`. -/
private def matVecMulCLM (qq : Mat d) : Vec d →L[ℝ] Vec d :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin qq)

private theorem matVecMulCLM_apply (qq : Mat d) (y : Vec d) :
    matVecMulCLM qq y = matVecMul qq y := by
  simp only [matVecMulCLM, LinearMap.coe_toContinuousLinearMap',
    Matrix.mulVecLin_apply, Geometry.matVecMul_eq_mulVec]

/-- Coordinatewise smoothness of the gradient field of the pulled-back cutoff
(`e.response.cutoff.estimate`; the cutoff class of `IsResponseCutoff`). -/
theorem contDiff_scalarCutoffGradientField_comp {d : ℕ} (qq : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec d => scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y i) := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => φ (matVecMul qq y)) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => matVecMul qq y) := by
      have heq : (fun y : Vec d => matVecMul qq y) = fun y => matVecMulCLM qq y := by
        funext y
        exact (matVecMulCLM_apply qq y).symm
      rw [heq]
      exact (matVecMulCLM qq).contDiff
    exact hφ.comp hlin
  exact contDiff_scalarCutoffGradientField_component hcomp i

/-- Bound on the derivative of a coordinate of the gradient field of the pulled-back cutoff by the
second-derivative bound the cutoff class carries (`e.response.cutoff.estimate`; the cutoff class
of `IsResponseCutoff`). -/
theorem norm_fderiv_scalarCutoffGradientField_comp_le {d : ℕ} (qq : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {B : ℝ}
    (hφ2 : ∀ x : Vec d,
      ‖iteratedFDeriv ℝ 2 (fun y : Vec d => φ (matVecMul qq y)) x‖ ≤ B) (i : Fin d) (z : Vec d) :
    ‖fderiv ℝ
        (fun y : Vec d => scalarCutoffGradientField (fun w : Vec d => φ (matVecMul qq w)) y i)
        z‖ ≤ B := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => φ (matVecMul qq y)) := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => matVecMul qq y) := by
      have heq : (fun y : Vec d => matVecMul qq y) = fun y => matVecMulCLM qq y := by
        funext y
        exact (matVecMulCLM_apply qq y).symm
      rw [heq]
      exact (matVecMulCLM qq).contDiff
    exact hφ.comp hlin
  exact fderiv_scalarCutoffGradientField_component_le_of_hessian_bound hψ i (hφ2 z)

/-- Bound on the gradient field of the pulled-back cutoff by the Lipschitz constant of the
pullback (`e.response.cutoff.estimate`; the cutoff class of `IsResponseCutoff`). -/
theorem norm_scalarCutoffGradientField_comp_le {d : ℕ} (qq : Mat d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {K : NNReal}
    (hlip : LipschitzWith K (fun y : Vec d => φ (matVecMul qq y))) (y : Vec d) :
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖ ≤ (K : ℝ) := by
  have _ := hφ
  calc
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖
        ≤ ‖fderiv ℝ (fun z : Vec d => φ (matVecMul qq z)) y‖ :=
          norm_scalarCutoffGradientField_le_fderiv _ _
    _ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hlip

end

end Homogenization.HighContrast.Multiscale
