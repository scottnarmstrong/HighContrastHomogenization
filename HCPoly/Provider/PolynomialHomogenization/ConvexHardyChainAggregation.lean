/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyChainMean
import HCPoly.Analytic.EuclideanAmbient
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyShadow
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyBallChain
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyRowFluctuation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyScaleSummation

/-!
# Aggregation of the small-radius part of convex Hardy chains

Successive chain links are aggregated only while their straight-chain shadows
fit inside the outer sandwich ball.  The complementary links are retained as
an explicit late-link term.  Thus the homogeneous shadow estimate is never
used beyond its geometric range.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- The Euclidean cross-diameter multiplier for two successive chain balls. -/
def convexHardyChainAggregationDistanceFactor
    (d : ℕ) (rho Rad : ℝ) : ℝ :=
  3 + Real.sqrt d * (Rad / rho)

end

end HighContrast
end Homogenization
