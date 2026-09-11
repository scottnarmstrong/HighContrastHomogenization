/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.SmallContrastVarianceLagged
import HCPoly.Provider.Quenched.SmallContrastAnnealedEnvelope
import HCPoly.Provider.Response.PreYoungFixedGridCells
import HCPoly.Provider.Response.ProfileRowSchur
import HCPoly.Provider.Response.ProfileRowSkewCarriers
import HCPoly.Provider.Response.ProfileRowOscillationSum
import HCPoly.Provider.Response.DiagonalWeakNormAdjointAlgebra
import HCPoly.Provider.Quenched.SmallContrastRowAtCenters
import HCPoly.Provider.Quenched.SmallContrastWeakValue
import HCPoly.Provider.Quenched.SmallContrastCenteringCap
import HCPoly.Provider.Quenched.SmallContrastTerminalComparability
import HCPoly.Provider.Quenched.SmallContrastSingleCellVariance
import HCPoly.Provider.Quenched.SmallContrastMeanDropCarrier
import HCPoly.Provider.Quenched.FixedGridWindowAccount
import HCPoly.Provider.Quenched.SmallContrastAlignedGeometry
import HCPoly.Provider.Quenched.Prop42Tilt.AdaptedHatIntrinsic
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope

/-!
# The entry lagged variance supply

The lagged variance supply against the entry-collapsed envelope and the
entry comparability: past the burn-in by the logarithm of the second
source moment, every excess-multiplying constant of the lagged value is
`kappaRef`-dimensional, with the source moments confined to the
concentration slot (which carries the subdivision decay) and the entry
delay.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The entry comparability constant. -/
def kap2Value (Cd g : ℝ) (mAl : Mat d) (G : ℕ) (E : BlockMat d) : ℝ :=
  kappaRef E * (2 * boundaryConst Cd g mAl * (3 : ℝ) ^ (g * (G : ℝ)))

end

end Homogenization.HighContrast.Quenched
