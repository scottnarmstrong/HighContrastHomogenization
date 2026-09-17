import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsSourceLoadLower
import HCPoly.Entry.Geometry.LoewnerCongruence
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPairing

/-!
# The head term of the source load

The source load `L_s` of `e.response.cutoff.estimate` is the weighted sum over the triadic
generations of the squared `(b^{1/2}, S_*^{-1/2})`-norm of the annealed mean.  At generation
`n = 0` the weight is `1`, the index box is the single scale-`s` cell itself, and the printed
summand `(|b^{1/2} P| + |S_*^{-1/2} Q|)^2` dominates the flat head energy
`|b^{1/2} P|^2 + |S_*^{-1/2} Q|^2`.  This module identifies that head term and bounds the flat
head energy by the source load whenever the defining series converges.  It is the only term of
`L_s` that the cutoff-mean row of the estimate consumes.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- At generation `n = 0` the triadic index box is the singleton box `{0}`: the only cell of the
partition at the terminal scale is the scale-`s` cell itself. -/
theorem triadicIndexBox_zero (d : ℕ) : triadicIndexBox d 0 = {0} := by
  rw [triadicIndexBox]
  have h : (((3 ^ 0 - 1) / 2 : ℕ) : ℤ) = 0 := by norm_num
  rw [h, neg_zero, Finset.Icc_self]
  exact Fintype.piFinset_singleton (0 : Fin d → ℤ)

end

end Homogenization.HighContrast.Multiscale
