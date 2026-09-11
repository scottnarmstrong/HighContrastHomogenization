/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects

/-!
# Arithmetic for source-coefficient bounds

This file records the scalar inequality shared by the bridge and transport
source-coefficient estimates.
-/

namespace Homogenization.HighContrast.Transport

/-- One plus a nonnegative multiple of `Π` is controlled by the common
`(2 + Π)` coefficient form. -/
theorem one_add_mul_le {M Pi X : ℝ} (hM : 0 ≤ M) (hPi : 1 ≤ Pi)
    (hX : 1 ≤ X) : 1 + M * Pi * X ≤ (1 + M) * (2 + Pi) * X := by
  have hPX : (0 : ℝ) ≤ Pi * X :=
    mul_nonneg (by linarith only [hPi]) (by linarith only [hX])
  have hMX : (0 : ℝ) ≤ M * X :=
    mul_nonneg hM (by linarith only [hX])
  have h1 : (1 : ℝ) ≤ (2 + Pi) * X := by linarith only [hX, hPX]
  have h2 : M * Pi * X ≤ M * ((2 + Pi) * X) := by linarith only [hMX]
  linarith only [h1, h2]

end Homogenization.HighContrast.Transport
