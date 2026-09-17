import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportXiDischarge
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportXiLp

/-!
# The bundled weight-field and Hessian hypotheses of the cutoff pairing bound

For a cutoff `φ` in the response cutoff class `IsResponseCutoff` and a matrix `qq`, the
negative-Besov duality bound behind `e.response.cutoff.estimate` consumes the weight field
`ξ = scalarCutoffGradientField (fun y => φ (qq y))` through its measurability, its uniform
first-order bound, and its resulting `L^∞` membership for the normalized reference-cube
measure; the same estimate consumes the nonnegativity of the second-order Hessian coefficient
carried by the cutoff class.  The declarations below discharge those four requirements directly
from membership in `IsResponseCutoff`, so that the hypotheses `hB`, `hξLp`, `hξ`, `hderiv` and
`hflux` of the pathwise cutoff pairing bound can be fed from the class instead of being carried
separately.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- The gradient field of the pulled-back cutoff of the response class is a.e. strongly measurable
for every measure on `Vec d` (`e.response.cutoff.estimate`). -/
theorem aestronglyMeasurable_xi {d : ℕ} (qq : Mat d) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (μ : MeasureTheory.Measure (Vec d)) :
    MeasureTheory.AEStronglyMeasurable
      (scalarCutoffGradientField (fun y => φ (matVecMul qq y))) μ := by
  have hcont : Continuous
      (scalarCutoffGradientField (fun y : Vec d => φ (matVecMul qq y))) := by
    refine continuous_pi ?_
    intro i
    exact (contDiff_xi_of_isResponseCutoff hφ i).continuous
  exact hcont.aestronglyMeasurable

/-- The gradient field of a cutoff of the response class is essentially bounded, hence `L^∞`, for
the normalized measure of the reference cube (`e.response.cutoff.estimate`). -/
theorem memLp_top_xi_of_isResponseCutoff {d : ℕ} [NeZero d] (qq : Mat d) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) :
    MeasureTheory.MemLp (scalarCutoffGradientField (fun y => φ (matVecMul qq y))) ∞
      (normalizedCubeMeasure (originCube d t)) := by
  have _ : NeZero d := inferInstance
  exact memLp_top_normalizedCubeMeasure_of_norm_le (originCube d t)
    (aestronglyMeasurable_xi qq hφ (normalizedCubeMeasure (originCube d t)))
    (norm_xi_le_of_isResponseCutoff hφ)

end

end Homogenization.HighContrast.Multiscale
