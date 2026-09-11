/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects

/-!
# The guarded denominator in the reverse bridge comparison

The comparison-scale smallness condition keeps the reverse-comparison
denominator positive and bounds its reciprocal by two.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

noncomputable section

/-- The guarded reverse-comparison denominator is strictly positive. -/
theorem one_sub_pos_of_le_half {z : ℝ} (hz : z ≤ 1 / 2) : 0 < 1 - z := by
  norm_num at hz ⊢
  linarith only [hz]

end

end Bridge
end HighContrast
end Homogenization
