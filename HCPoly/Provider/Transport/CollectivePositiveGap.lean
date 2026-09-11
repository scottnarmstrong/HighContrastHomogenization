/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.PositiveGapClosure
import HCPoly.Provider.Recurrence.PositiveGapIntegration

open MeasureTheory
namespace Homogenization
namespace HighContrast
namespace Transport
open scoped ENNReal

/-! Scalar absorption needed by a collective positive-gap estimate. -/

/-- A single absorption pays a shared fluctuation and a collective defect budget. -/
theorem collective_gap_absorption {Q C K f x y B : ℝ}
    (hQ : 2 ≤ Q) (hC : 0 < C) (hK : 0 ≤ K)
    (hf : 0 ≤ f) (hx : 0 ≤ x) (hy : 0 ≤ y) (hB : 0 ≤ B)
    (habsorb : x ^ Q ≤ C * B + C * y ^ (Q - 1) * x)
    (htri : f ≤ K * (y + x + B ^ Q⁻¹)) :
    f ^ Q ≤
      (K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹)) ^ Q *
        (2 : ℝ) ^ (Q - 1) * (y ^ Q + B) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_two hQ
  have hxbound := Recurrence.le_rpow_add_of_rpow_le hQ hC hx hy zero_le_one hB
    (by simpa using habsorb)
  norm_num at hxbound
  have h2C : 0 ≤ (2 * C) ^ Q⁻¹ := Real.rpow_nonneg (by positivity) _
  have h2C' : 0 ≤ (2 * C) ^ (Q - 1)⁻¹ := Real.rpow_nonneg (by positivity) _
  have hroot : 0 ≤ B ^ Q⁻¹ := Real.rpow_nonneg hB _
  have hlin : y + x + B ^ Q⁻¹ ≤
      (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) * (y + B ^ Q⁻¹) := by
    nlinarith only [hxbound, hy, hroot, h2C, h2C']
  have hpre : f ≤ K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) *
      (y + B ^ Q⁻¹) := by
    calc f ≤ K * (y + x + B ^ Q⁻¹) := htri
      _ ≤ K * ((1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) *
          (y + B ^ Q⁻¹)) := mul_le_mul_of_nonneg_left hlin hK
      _ = _ := by ring
  have hfac0 : 0 ≤ K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) :=
    mul_nonneg hK (by linarith only [h2C, h2C'])
  have hp := Real.rpow_le_rpow hf hpre hQ0.le
  rw [Real.mul_rpow hfac0 (add_nonneg hy hroot)] at hp
  have hadd := Recurrence.rpow_add_le_two_rpow_mul_add hy hroot (by linarith only [hQ])
  have hrootQ : (B ^ Q⁻¹) ^ Q = B := by
    rw [← Real.rpow_mul hB, inv_mul_cancel₀ (ne_of_gt hQ0), Real.rpow_one]
  rw [hrootQ] at hadd
  refine hp.trans ?_
  have hm := mul_le_mul_of_nonneg_left hadd (Real.rpow_nonneg hfac0 Q)
  nlinarith only [hm]

end Transport
end HighContrast
end Homogenization
