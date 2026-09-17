import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Assembling the cutoff rows of `e.response.cutoff.estimate`

The cutoff energy defect and the centred cutoff-mean row enter the cutoff estimate with the two
bounds `C (τ + (τ E[J])^{1/2} + g E[J])` and `C (τ L)^{1/2} + C g (E[J] L)^{1/2}`, while the
cutoff pairing row enters with coefficient one.  Once the response `J` is split into these three
rows, the printed right-hand side of `e.response.cutoff.estimate` follows by linear arithmetic.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- The response split with half weight on the pairing row: if
`|J| ≤ (1 / 2) * pair + row1 + row2` and the two rows obey their printed bounds, then `|J|` is
bounded by the printed right-hand side of `e.response.cutoff.estimate` with the pairing row
carried at coefficient one.  The half weight is absorbed using the nonnegativity of `pair`. -/
theorem le_cutoffRows_of_two_rows {C τ EJ L g pair row1 row2 J : ℝ}
    (hsplit : |J| ≤ (1 / 2 : ℝ) * pair + row1 + row2)
    (hpair : 0 ≤ pair)
    (hrow1 : row1 ≤ C * (τ + Real.sqrt (τ * EJ) + g * EJ))
    (hrow2 : row2 ≤ C * Real.sqrt (τ * L) + C * (g * Real.sqrt (EJ * L))) :
    |J| ≤ C * (τ + Real.sqrt (τ * EJ) + g * EJ)
        + C * Real.sqrt (τ * L)
        + C * (g * Real.sqrt (EJ * L))
        + pair := by
  linarith only [hsplit, hpair, hrow1, hrow2]

end

end Homogenization.HighContrast.Multiscale
