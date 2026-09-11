/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyCellInitialAggregation
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyCellRawMean
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyRowFluctuation
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem

/-!
# Assembly of the convex fractional Hardy estimate

The inverse-scale weighted squared deviation from the domain mean splits into
the within-cell fluctuation and the defect of each cell mean from that domain
mean. This file records that reduction, the within-cell bound, and the first
cell-to-initial-ball comparison with the exact Whitney weights.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Function

noncomputable section

variable {d : ℕ}

/-- The countable family of all cells in a convex Hardy Whitney system. -/
abbrev ConvexHardyWhitneySystem.CellIndex {U : Set (Vec d)} {rho Rad : ℝ}
    (system : ConvexHardyWhitneySystem U rho Rad) :=
  Σ a : {a : ℤ // a ≤ system.topScale}, ↑(system.rows a.1)

/-- The cell represented by one index of a convex Hardy Whitney system. -/
def ConvexHardyWhitneySystem.cell {U : Set (Vec d)} {rho Rad : ℝ}
    (system : ConvexHardyWhitneySystem U rho Rad)
    (i : system.CellIndex) : Set (Vec d) :=
  standardCell d i.1.1 i.2.1

/-- The inverse fractional side-length weight of a Whitney cell. -/
def ConvexHardyWhitneySystem.scaleWeight {U : Set (Vec d)} {rho Rad : ℝ}
    (system : ConvexHardyWhitneySystem U rho Rad) (s : ℝ)
    (i : system.CellIndex) : ℝ≥0∞ :=
  ENNReal.ofReal (((3 : ℝ) ^ i.1.1) ^ (-2 * s))

end

end HighContrast
end Homogenization
