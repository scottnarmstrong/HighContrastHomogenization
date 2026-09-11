/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyCellRawMean
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyRowFluctuation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Aggregating the initial cell-to-ball comparisons

The first link from a Whitney cell to its ball chain is charged through the
cell coordinate of a disjoint family of product rectangles.  Its scale
weight cancels the inverse cell and ball volumes without any summation loss.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Function

noncomputable section

variable {d : ℕ}

/-- The scale-free coefficient for all initial cell-to-ball comparisons. -/
def convexHardyCellInitialAggregationConstant
    (d : ℕ) (s rho Rad : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((Real.sqrt d) ^ d *
      Real.rpow
        (2 * (1 + Real.sqrt d * (1 + Rad / rho)))
        ((d : ℝ) + 2 * s))

end

end HighContrast
end Homogenization
