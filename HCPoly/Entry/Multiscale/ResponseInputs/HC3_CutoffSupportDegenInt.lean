import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportDegenerate
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportWeak
import HCPoly.Entry.Geometry.CanonicalMetricBounds

/-!
# The singular-grid branch of the annealed cutoff pairing bound

The cutoff pairing of the response estimate is an expectation of absolute volume averages of an
adapted cell.  When the selected grid is singular the adapted cell is Lebesgue null, so every such
average is the junk value `0` and the expectation vanishes.  Together with the metric dichotomy
for the canonical metric, which always places an arbitrary doubled block on either the positive
definite branch or the singular-grid branch, this disposes of the branch on which the change of
variables underlying the cutoff argument is unavailable.

Paper: `e.response.cutoff.estimate`, `e.scale.selection.canonical.metric`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- On a singular grid `q` every adapted cell is Lebesgue null, so the absolute volume average of
any function over it is the junk value `0`; consequently the integral of those absolute averages
against any measure vanishes.  This is the degenerate branch of the cutoff pairing of
`e.response.cutoff.estimate`. -/
theorem integral_abs_volumeAverage_adaptedCell_eq_zero_of_det_eq_zero {d : ℕ}
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.det = 0) (t : ℤ)
    (f : CoeffSpace d → Vec d → ℝ) :
    (∫ a, |volumeAverage (HighContrast.adaptedCell q t) (f a)| ∂P) = 0 := by
  have h : ∀ a, |volumeAverage (HighContrast.adaptedCell q t) (f a)| = 0 := fun a => by
    rw [volumeAverage_adaptedCell_eq_zero_of_det_eq_zero hq t (f a), abs_zero]
  simp only [h, integral_zero]

/-- The canonical metric of an arbitrary doubled block is either positive definite or so
degenerate that the selected grid it produces is singular.  No symmetry or positivity hypothesis is
needed, because the junk values of the square root and of the matrix inverse are themselves
positive semidefinite.  This is the dichotomy of `e.scale.selection.canonical.metric` that selects
the branch of `e.response.cutoff.estimate`. -/
theorem metric_posDef_or_respGrid_det_eq_zero {d : ℕ} [NeZero d] (jStar : ℕ) (F : BlockMat d) :
    (explicitCanonicalMetric F).PosDef ∨ (respGrid jStar F).det = 0 :=
  Geometry.explicitCanonicalMetric_posDef_or_det_roundedGrid_eq_zero jStar F

end

end Homogenization.HighContrast.Multiscale
