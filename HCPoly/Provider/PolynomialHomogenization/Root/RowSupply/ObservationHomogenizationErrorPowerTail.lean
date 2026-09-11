/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.ObservationNormalizedResponseParentRow
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.DescendantCoefficientRestriction
import HCPoly.Provider.PolynomialHomogenization.ConvexWhitneyGeometry
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.HomogenizationErrorAllDepthMajorant
import HCPoly.Provider.Regularity.RoundedOuterScaleFubini
import HCPoly.Provider.Regularity.QuantitativeGoodTail

/-!
# Observation homogenization error from a reference power tail

The descendant filling kernel and the all-depth Besov weight are regrouped
into one nonnegative convolution.  Its parent row is exactly the squared
scalar identity weak error and is therefore priced by the retained power
tail once the parent lies beyond the activation generation.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The uniform boundary coefficient in the affine observation filling. -/
noncomputable def observationFillingCoefficient
    (d : ℕ) (epsilon : ℝ) (abar : Mat d) : ℝ :=
  max 1 (6 * (d : ℝ) * Real.sqrt d *
    ‖(epsilonAffineGrid epsilon abar)⁻¹ *
      Selection.normalizedRoot (symmPart abar)‖)

/-- The honest pointwise majorant for the observation descendant row. -/
noncomputable def observationParentRowMajorant
    [NeZero d] (epsilon : ℝ) (abar : Mat d)
    (aRef : Book.Ch03.CoeffFamily d) (M K : ℤ) (l : ℕ) : ℝ :=
  ∑' u : ℕ,
    (observationFillingCoefficient d epsilon abar *
      (3 : ℝ) ^ (-(u : ℤ))) *
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d M) (K - (l : ℤ) - (u : ℤ)) aRef (1 : Mat d)

/-- The exact convolution loss multiplying the squared parent weak error. -/
noncomputable def observationParentConvolutionFactor
    (d : ℕ) (s epsilon : ℝ) (abar : Mat d) (M K : ℤ) : ℝ :=
  (observationFillingCoefficient d epsilon abar *
      (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹) *
    Real.rpow (3 : ℝ) (2 * s * ((M - K).toNat : ℝ))

end

end RowSupply
end HighContrast
end Homogenization
