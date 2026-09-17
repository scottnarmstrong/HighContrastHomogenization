import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentDegenerate
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedEnergy

/-!
# The cell-average lemma on the degenerate metric branch

The cell-average estimate `l.weaknorms.moreproto` is stated for an arbitrary doubled block `F`,
so its metric `m = explicitCanonicalMetric F` may degenerate.  `HC2b_DiagonalWeakRecentDegenerate.lean`
classifies the degenerations; this file cashes the first of them in at the level of the estimate
itself.

Two statements:

* the right-hand side of the estimate is nonnegative for every `γ ∈ [0,1)` — every factor is a
  square root, a nonnegative weight, or one of the two nonnegative finite sums, and the only
  hypothesis used is `γ < 1`, which makes the printed coefficient `16 / (1 - ρ(γ))` positive;
* when the metric vanishes the estimate holds outright, because `M₀^{1/2}` annihilates every
  doubled vector, so the whole left-hand side is `0`.

Together these close the branch `¬ IsUnit (explicitCanonicalMetric F).det` of the estimate, which by
`explicitCanonicalMetric_eq_zero_of_not_isUnit` is exactly the branch `explicitCanonicalMetric F = 0`.

Two further statements record that, at the estimate's own binders, that branch is in fact EMPTY:
the estimate carries `IsUnit (respGrid jStar F)`, and the metric dichotomy
`explicitCanonicalMetric_posDef_or_det_roundedGrid_eq_zero` — which holds for an arbitrary `F`, with no
symmetry and no positivity — turns a unit grid into a positive definite metric, hence into a
positive definite `M₀`.  So the `M₀` positivity that the recent-head chain asks for is free at
the estimate, and the degenerate metric branches never arise there.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The metric of `F` is positive definite as soon as the selected grid is a unit.  The metric
dichotomy holds for an arbitrary doubled block, so no symmetry or positivity of `F` is needed:
a degenerate metric forces a singular grid, which a unit grid excludes. -/
theorem h6a_explicitCanonicalMetric_posDef_of_isUnit_respGrid {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) : (explicitCanonicalMetric F).PosDef := by
  rcases Geometry.explicitCanonicalMetric_posDef_or_det_roundedGrid_eq_zero jStar F with hpos | hdet
  · exact hpos
  · exfalso
    have hu : IsUnit (respGrid jStar F).det := (Matrix.isUnit_iff_isUnit_det _).mp hgrid
    rw [respGrid, hdet] at hu
    exact (not_isUnit_zero (M₀ := ℝ)) hu

/-- Consequently the doubled metric block `M₀ = diag(m, m⁻¹)` is positive definite at the
estimate's own binders. -/
theorem h6a_respM0_posDef_of_isUnit_respGrid {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) : (toFullBlockMat (respM0 F)).PosDef :=
  h4_respM0_full_posDef (h6a_explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid)

end

end Homogenization.HighContrast.Multiscale
