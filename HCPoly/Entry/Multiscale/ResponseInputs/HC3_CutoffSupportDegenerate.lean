import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock

/-!
# The singular-grid branch of the cutoff pairing bound

The selected grid is `respGrid jStar F = Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)`, and
every entry of `Geometry.explicitRoundedGrid` carries a factor built from the inverse of its metric
argument.  Mathlib's matrix inverse of a singular matrix is `0`
(`Matrix.nonsing_inv_apply_not_isUnit`), so when the canonical metric is singular the selected
grid degenerates to the zero matrix and the adapted cell carries no Lebesgue volume.  This file
records those degenerations: every volume average over a degenerate adapted cell is the junk value
`0`, and the determinant of the degenerate selected grid vanishes.

-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- On a singular grid `q` the adapted cell `HighContrast.adaptedCell q t` is Lebesgue null, so every
volume average over it is the junk value `0`.  Indeed
`Geometry.volume_adaptedCell_toReal` gives
`(volume (HighContrast.adaptedCell q t)).toReal = |q.det| * ((3 : ℝ) ^ t) ^ d`, which vanishes when
`q.det = 0`, and `volumeAverage` multiplies by the inverse of that volume. -/
theorem volumeAverage_adaptedCell_eq_zero_of_det_eq_zero {d : ℕ} {q : Mat d} (hq : q.det = 0)
    (t : ℤ) (f : Vec d → ℝ) : volumeAverage (HighContrast.adaptedCell q t) f = 0 := by
  unfold volumeAverage
  rw [Geometry.volume_adaptedCell_toReal q t, hq]
  simp

end

end Homogenization.HighContrast.Multiscale
