/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyChainAggregation
/-!
# Fractional aggregation of the small-radius Hardy-chain links

The homogeneous part of the coherent ball chains is summed through a
pointwise shadow estimate.  The physical pair distance is retained until the
dyadic scale sum, avoiding a logarithmic loss over the remaining chain depth.
-/

namespace Homogenization
namespace HighContrast
open MeasureTheory
open scoped ENNReal Matrix
attribute [local instance] Classical.propDecidable

noncomputable section
variable {d : ℕ}

/-- The explicit coefficient for aggregating all small-radius chain links. -/
def convexHardyEarlyAggregationConstant
    (d : ℕ) (s beta rho Rad : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (convexHardyShadowRowConstant d rho Rad
          (convexHardyChainAggregationDistanceFactor d rho Rad) *
        ((d : ℝ) / 8) ^ d) *
    convexHardyScaleSummationConstant d s beta
      (convexHardyChainAggregationDistanceFactor d rho Rad)

end
end HighContrast
end Homogenization
