/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.RoundedOuterSpatialResponsePowerTail
import HCPoly.Provider.Regularity.CommonQuantitativeAffineScale

/-!
# Rounded outer response tails at the common effective scale

The dimension-only rounded-response amplitude is identified with the R3-A
affine loss.  Its already multiplier is then used once to rebase the
negative power from the R1 scale to the common R1/R3 effective scale.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem multiplier_rpow_mul_ratio_eq_rpow_mul_scale
    {mult kappa x r : ℝ} (hmult : 0 < mult)
    (hx : 0 < x) (hr : 0 < r) :
    mult ^ kappa * (r / x) ^ (-kappa) =
      (r / (mult * x)) ^ (-kappa) := by
  have hratio : r / (mult * x) = (r / x) / mult := by
    field_simp [hmult.ne', hx.ne']
  rw [hratio, Real.div_rpow (div_nonneg hr.le hx.le) hmult.le,
    Real.rpow_neg hmult.le, div_inv_eq_mul, mul_comm]

end

end Transport
end HighContrast
end Homogenization
