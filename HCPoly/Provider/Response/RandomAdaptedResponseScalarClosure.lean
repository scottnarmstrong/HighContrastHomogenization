/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseScalarAllocation

/-!
# Literal compact response closure

The actual weak quantity and the two one-sign compact bounds are closed at
the response-window coefficient.
-/

namespace Homogenization.HighContrast.Response

open scoped ENNReal

noncomputable section

/-- Squaring a mixed weak-root estimate retains the extended-nonnegative
weak quantity and produces the response-window scale exactly. -/
theorem weak_quantity_le_of_root_bound
    {W N : ℝ≥0∞} {R kappa : ℝ}
    (hW : W = N ^ (2 : ℕ)) (hR : 0 ≤ R) (hkappa : 0 ≤ kappa)
    (hroot : N ≤ ENNReal.ofReal (R * Real.sqrt kappa)) :
    W ≤ ENNReal.ofReal (R ^ 2 * kappa) := by
  rw [hW]
  calc
    N ^ (2 : ℕ) ≤ ENNReal.ofReal (R * Real.sqrt kappa) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (zero_le N) hroot 2
    _ = ENNReal.ofReal ((R * Real.sqrt kappa) ^ (2 : ℕ)) := by
      rw [ENNReal.ofReal_pow (mul_nonneg hR (Real.sqrt_nonneg kappa))]
    _ = ENNReal.ofReal (R ^ 2 * kappa) := by
      congr 1
      rw [mul_pow, Real.sq_sqrt hkappa]

/-- A carried compact pre-Young right-hand side at the literal defect,
terminal energy, hatted row, and weak quantity has the one-sign response
allocation. -/
theorem literal_compact_pre_young_allocation
    {C expo T A L R kappa tau EJ : ℝ} {row weak : ℝ≥0∞}
    (hC : 0 ≤ C) (hexpo : 0 ≤ expo)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hkappa : 1 ≤ kappa)
    (htau : tau ≤ T * Real.sqrt kappa)
    (hEJ : EJ ≤ A * Real.sqrt kappa)
    (hrow : row ≤ ENNReal.ofReal (L * kappa ^ (3 / 2 : ℝ)))
    (hweak : weak ≤ ENNReal.ofReal (R ^ 2 * kappa)) :
    ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt tau) *
          (ENNReal.ofReal (Real.sqrt tau) +
            ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * ENNReal.ofReal expo *
          ENNReal.ofReal (Real.sqrt EJ) *
            (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * weak ≤
      ENNReal.ofReal
        (C * (T + Real.sqrt (T * A) + Real.sqrt (T * L) +
          expo * (A + Real.sqrt (A * L)) + R ^ 2) * kappa) := by
  obtain ⟨haa, hab, har, hbb, hbr⟩ :=
    calibrated_mixed_products hT hA hL hkappa htau hEJ hrow
  exact compact_pre_young_allocation hC hexpo hT (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hA (Real.sqrt_nonneg _) (sq_nonneg R)
    (le_trans zero_le_one hkappa) haa hab har hbb hbr hweak

/-- The two equal one-sign allocations are exactly the normalized response
coefficient used by the supremum insertion. -/
theorem two_half_allocations
    {C scalar kappa omega : ℝ} {minus plus : ℝ≥0∞}
    (hC : 0 ≤ C) (hscalar : 0 ≤ scalar) (hkappa : 0 ≤ kappa)
    (homega : omega = 2 * C * scalar)
    (hminus : minus ≤ ENNReal.ofReal (C * scalar * kappa))
    (hplus : plus ≤ ENNReal.ofReal (C * scalar * kappa)) :
    minus + plus ≤ ENNReal.ofReal (omega * kappa) := by
  have hhalf : 0 ≤ C * scalar * kappa :=
    mul_nonneg (mul_nonneg hC hscalar) hkappa
  calc
    minus + plus ≤
        ENNReal.ofReal (C * scalar * kappa) +
          ENNReal.ofReal (C * scalar * kappa) :=
      add_le_add hminus hplus
    _ = ENNReal.ofReal (C * scalar * kappa + C * scalar * kappa) := by
      rw [ENNReal.ofReal_add hhalf hhalf]
    _ = ENNReal.ofReal (omega * kappa) := by
      congr 1
      rw [homega]
      ring

end

end Homogenization.HighContrast.Response
