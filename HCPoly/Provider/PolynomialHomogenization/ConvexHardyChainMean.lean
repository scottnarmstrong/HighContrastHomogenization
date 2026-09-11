/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyBallChain
import HCPoly.Analytic.EuclideanAmbient
import HCPoly.Provider.PolynomialHomogenization.FractionalMeanJump
import HCPoly.Analytic.AntiVacuityInstances

/-!
# Fractional control of means along convex ball chains

Successive balls in a convex Hardy chain have doubling radii and quantitatively
nearby centers.  The fractional mean-jump estimate therefore controls each
successive change of mean by the Gagliardo energy on the union of the two
balls.  Finite vector telescoping then compares the initial mean with the mean
on the fixed core ball.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit lower bound for the volume of a Euclidean ball of radius
`r`, obtained from the concentric ambient sup-norm ball. -/
def convexHardyBallVolumeLower (d : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d)

end

end HighContrast
end Homogenization
