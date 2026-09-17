import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The head/tail split of a scale-average sum, generic

The cell-average argument splits the scale-average seminorm at the window depth `H`. The tree
proves that split only privately, tied to the cell-average family, so no consumer above can reuse
it.  This module proves the two series facts the split rests on, for an arbitrary summable real
family: the split itself, and the geometric bound on the shifted tail.  Nothing here mentions a
cell, a coefficient field, or a seminorm, so the module sits below every carrier and can be used
on either side of the estimate.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- Splitting a summable real series at an index `H + 1`: the full sum is the finite head over
`range (H + 1)` plus the tail whose indices are shifted by `H + 1`. -/
theorem h6a_tsum_split_range {f : ℕ → ℝ} (hf : Summable f) (H : ℕ) :
    ∑' n : ℕ, f n = (∑ n ∈ Finset.range (H + 1), f n) + ∑' n : ℕ, f (n + (H + 1)) :=
  (hf.sum_add_tsum_nat_add (H + 1)).symm

end

end Homogenization.HighContrast.Multiscale
