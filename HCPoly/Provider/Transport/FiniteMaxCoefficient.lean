/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteCellMajorantMaxSplit

/-!
# Real form of the three-maximum splitting coefficient
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped ENNReal

noncomputable section

/-- The extended-real coefficient of the three-maximum split is the image of
its finite real counterpart. -/
theorem finite_max_split_coefficient_eq_ofReal (d : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ENNReal.ofReal ((2 * (d : ℝ)) ^ 2) ^ Q *
        ((2 : ℝ≥0∞) ^ (Q - 1)) ^ 2 =
      ENNReal.ofReal
        ((((2 * (d : ℝ)) ^ 2) ^ Q) * (((2 : ℝ) ^ (Q - 1)) ^ 2)) := by
  have hbase0 : 0 ≤ (2 * (d : ℝ)) ^ 2 := sq_nonneg _
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hQm0 : 0 ≤ Q - 1 := sub_nonneg.mpr hQ
  have htwo0 : (0 : ℝ) ≤ 2 := by norm_num
  have hleft0 : 0 ≤ ((2 * (d : ℝ)) ^ 2) ^ Q :=
    Real.rpow_nonneg hbase0 Q
  have htwoPow0 : 0 ≤ (2 : ℝ) ^ (Q - 1) :=
    Real.rpow_nonneg htwo0 (Q - 1)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg hbase0 hQ0,
    ENNReal.ofReal_rpow_of_nonneg htwo0 hQm0,
    ← ENNReal.ofReal_pow htwoPow0, ← ENNReal.ofReal_mul hleft0]

end

end Transport
end HighContrast
end Homogenization
