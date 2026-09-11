/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyCellRawMean
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyChainAggregation
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyCoreMean

/-!
# Fixed-cutoff aggregation for convex Hardy chains

A common dyadic cutoff replaces the uniformly interior tail of every ball
chain by one comparison with the domain mean.  Short chains use their initial
ball, so the construction has no exceptional row.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

namespace ConvexHardyBallChain

end ConvexHardyBallChain

/-- The explicit normalized cutoff-mean aggregation factor. -/
def convexHardyCutoffAggregationFactor
    (d : ℕ) (rho Rad s : ℝ) (K : ℕ) (n : ℤ) : ℝ≥0∞ :=
  convexHardyCoreRowMassFactor d rho s n *
    convexHardyCoreMeanFactor d (convexHardyDyadicRadius rho K) Rad s

/-- The infinite geometric-head factor used for the boundary-scale chain
prefix. -/
def convexHardyPrefixGeometricFactor (beta : ℝ) : ℝ≥0∞ :=
  (1 - ENNReal.ofReal (Real.rpow 2 (-beta)))⁻¹

end

end HighContrast
end Homogenization
