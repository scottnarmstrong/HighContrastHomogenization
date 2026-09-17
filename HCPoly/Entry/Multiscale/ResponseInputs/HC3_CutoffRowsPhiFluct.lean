import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The fluctuation of a response cutoff

A response cutoff `φ` of `e.response.cutoff.estimate` lies in `[0, 2]` and has volume average
one on its terminal cell, so its fluctuation `φ - 1` is bounded by one pointwise and has mean
zero on that cell.  Mean zero is what allows any constant to be subtracted from the factor paired
with the fluctuation without changing the weighted average: the centring step of the cutoff-mean
rows of the response-transfer estimate.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A response cutoff `φ` takes values in `[0, 2]`, so its fluctuation `φ - 1` is bounded by one
in absolute value at every point: `|φ x - 1| ≤ 1`. -/
theorem abs_isResponseCutoff_sub_one {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (x : Vec d) : |φ x - 1| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith only [hφ.1 x]
  · linarith only [hφ.2.1 x]

end

end Homogenization.HighContrast.Multiscale
