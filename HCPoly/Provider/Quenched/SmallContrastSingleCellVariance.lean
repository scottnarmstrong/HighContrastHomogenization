/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.SmallContrastTerminalComparability
import HCPoly.Provider.Quenched.SmallContrastWeakCellVariance
import HCPoly.Provider.Quenched.SmallContrastSourceMoment
import HCPoly.Provider.Transport.WindowCenteredBound

/-!
# The single-cell reference variance at arbitrary enclosed scales

The per-scale fluctuation carrier of the weak cap is bounded by an explicit
constant at every enclosed scale: the coarse block and the adapted mean are
both dominated by the scaled reference with the normalized-source-scale
factor, the Loewner sandwich bounds the normalized Schatten size pointwise,
and the crude second moment of the normalized source scale integrates the
bound.  This is the printed crude-moment display for the single-cell
variance, window-free.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder ENNReal

noncomputable section

variable {d : ℕ}

/-- The second crude moment constant of the normalized source scale. -/
def sourceMomentTwo (K : ℝ) : ℝ :=
  1 + 2 * ((2 : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
    growthBar K ^ IndependentSums.natTriangular 2

end

end Homogenization.HighContrast.Quenched
