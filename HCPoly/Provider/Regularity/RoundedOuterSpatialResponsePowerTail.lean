/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Entry.EuclideanAdapter
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootCoefficient
import HCPoly.Provider.Regularity.RoundedAffineMap
import HCPoly.Provider.Selection.EnclosureGeometry
import HCPoly.Provider.Regularity.RoundedOuterScaleFubini
import HCPoly.Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity
import HCPoly.Provider.Entry.AdapterQuadratic
import HCPoly.Provider.Regularity.RoundedNormalizedRootCellResponseMax
import HCPoly.Provider.Response.AdaptedLinearOscillation
import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
import HCPoly.Provider.Regularity.QuantitativeGoodTail
import HCPoly.Provider.Initialization.Boundary

/-!
# Quantitative power tails for rounded outer response maxima

The retained scalar identity power tail is applied at the enclosing
normalized-root parent.  The parent shift and rounded boundary losses are
then bounded by one dimension-only affine constant times the witness
eccentricity.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped BigOperators Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

private noncomputable def roundedOuterResponseAffineConstantSq (d : ℕ) : ℝ :=
  max 1
      (6 * (d : ℝ) * Real.sqrt d * (101 / 100 : ℝ)) *
    10 *
      (1 + 3 * ((100 / 99 : ℝ) * Real.sqrt d))

/-- A dimension-only constant absorbing the rounded boundary row and the
normalized-root parent shift on the weak-error scale. -/
noncomputable def roundedOuterResponseAffineConstant (d : ℕ) : ℝ :=
  Real.sqrt (roundedOuterResponseAffineConstantSq d)

theorem roundedOuterResponseAffineConstant_pos (d : ℕ) :
    0 < roundedOuterResponseAffineConstant d := by
  unfold roundedOuterResponseAffineConstant roundedOuterResponseAffineConstantSq
  apply Real.sqrt_pos.2
  have hfirst : 0 < max 1
      (6 * (d : ℝ) * Real.sqrt d * (101 / 100 : ℝ)) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlast : 0 < 1 + 3 * ((100 / 99 : ℝ) * Real.sqrt d) := by
    positivity
  exact mul_pos (mul_pos hfirst (by norm_num)) hlast

end

end Transport
end HighContrast
end Homogenization
