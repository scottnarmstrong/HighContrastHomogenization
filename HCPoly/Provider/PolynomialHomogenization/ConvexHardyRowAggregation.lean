/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyEndpoint
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyInitialMeanAggregation
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem

/-!
# Fractional Hardy aggregation on convex domains

The initial Whitney-cell comparison and a stopped convex ball chain control
the centered inverse-scale weighted squared-deviation term in the positive
fractional row norm.  The existential form chooses all auxiliary geometric
parameters before the function being estimated.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit coefficient for the centered positive Whitney-row energy. -/
def convexHardyWhitneyRowAggregationFactor
    (d : ℕ) (rho Rad s beta : ℝ) (K : ℕ) (n : ℤ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal ((Real.sqrt d) ^ ((d : ℝ) + 2 * s)) +
    4 * convexHardyCellInitialAggregationConstant d s rho Rad +
    4 * convexHardyInitialToDomainMeanAggregationFactor
      d rho Rad s beta K n

end

end HighContrast
end Homogenization
