/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.AffineNegSobolevNorm
import HCPoly.Provider.Initialization.IdentityGrid
import HCPoly.Provider.PolynomialHomogenization.NegativeSobolevCubeDuality
import HCPoly.Setup.Geometry
import Homogenization.Book.Ch03.ABK26.FluxComparisonLocalization
import Homogenization.Sobolev.Fractional.CenteredCubeFractionalCZFullNorm
import Homogenization.Sobolev.Fractional.EuclideanWspSmoothDualFieldPairing
import Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-!
# Scalar flux comparison on centered cubes

This file specializes the centered-cube flux comparison to exponent two and
the identity scalar comparator, then converts the smooth-dual norm to the
compact-test negative Sobolev norm below order one half.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem scalarMatrix_one_eq_one {d : ℕ} :
    scalarMatrix (d := d) (1 : ℝ) = (1 : Mat d) := by
  ext i j
  simp [scalarMatrix, Matrix.one_apply]

end

end HighContrast
end Homogenization
