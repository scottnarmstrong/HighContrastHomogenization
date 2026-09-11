/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorDecay.AffineNegOneTransport
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootCoefficient

namespace Homogenization
namespace HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The determinant contribution to affine `H¹` distortion is controlled by
the Euclidean operator norm with a dimension-only factor. -/
theorem absDet_rpow_two_div_le
    {d : ℕ} [NeZero d] (L : Mat d) :
    |L.det| ^ ((2 : ℝ) / (d : ℝ)) ≤
      (Real.sqrt d * ‖L‖) ^ 2 := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  let B : ℝ := Real.sqrt d * ‖L‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hdet : |L.det| ≤ B ^ d := by
    simpa only [B] using Transport.abs_det_le_pow_norm L
  have hroot := Real.rpow_le_rpow (abs_nonneg L.det) hdet
    (inv_nonneg.mpr hd.le)
  rw [Real.pow_rpow_inv_natCast hB (NeZero.ne d)] at hroot
  have hsquare := pow_le_pow_left₀
    (Real.rpow_nonneg (abs_nonneg L.det) _) hroot 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg L.det)] at hsquare
  have hexp : (d : ℝ)⁻¹ * (2 : ℝ) = 2 / (d : ℝ) := by
    rw [div_eq_mul_inv, mul_comm]
  simpa only [Nat.cast_ofNat, hexp, B] using hsquare

end


end HighContrast
end Homogenization
