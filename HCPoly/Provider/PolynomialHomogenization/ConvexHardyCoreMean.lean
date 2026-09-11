/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyChainMean
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Inverse-scale row mass in a convex Whitney system

The Whitney row-volume estimate and a geometric series control the total
normalized inverse-scale mass of the cells. The retained factors support
the fixed-cutoff aggregation of boundary and top rows.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The loss in comparing the mean on the common interior ball with the
domain mean. -/
def convexHardyCoreMeanFactor (d : ℕ) (rho Rad s : ℝ) : ℝ≥0∞ :=
  2 * (convexHardyBallVolumeLower d rho)⁻¹ *
    ENNReal.ofReal ((2 * Rad) ^ ((d : ℝ) + 2 * s))

/-- The ratio of the inverse-scale Whitney row series. -/
def convexHardyCoreRowRatio (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 3 : ℝ) ^ (-2 * s)) * ENNReal.ofReal (1 / 3 : ℝ)

/-- The normalized total inverse-scale volume bound for all Whitney rows up
to the top scale `n`. -/
def convexHardyCoreRowMassFactor (d : ℕ) (rho s : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (((3 : ℝ) ^ n) ^ (-2 * s)) +
    ENNReal.ofReal (((3 : ℝ) ^ (n - 1)) ^ (-2 * s)) *
      ENNReal.ofReal
        (6 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ (n - 1) / rho) *
        (1 - convexHardyCoreRowRatio s)⁻¹

end

end HighContrast
end Homogenization
