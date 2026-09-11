/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects

/-!
# Scale facts for the two-grid bridge

This file proves the elementary exponent, grid-factor, and scale-range facts
used by the two-grid comparisons and the shifted determinant drift.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The cross-grid factor is at least one. -/
theorem one_le_gridRatio (q q' : Mat d) : 1 ≤ gridRatio q q' := by
  unfold gridRatio
  have h₁ : 0 ≤ ‖q⁻¹ * q'‖ := norm_nonneg _
  have h₂ : 0 ≤ ‖(q')⁻¹ * q‖ := norm_nonneg _
  exact one_le_pow₀ (by linarith only [h₁, h₂])

/-- The bridge drift exponent is one eighth of the unused growth exponent. -/
theorem initExpRhoDr_eq (g : ℝ) : initExpRhoDr g = (1 - g) / 8 := by
  rw [initExpRhoDr, initExpA]
  ring

/-- The bridge drift exponent is positive in the source regime. -/
theorem initExpRhoDr_pos {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < initExpRhoDr g := by
  rw [initExpRhoDr_eq]
  linarith only [hg.2]

/-- The bridge drift exponent is strictly below the unused growth exponent. -/
theorem initExpRhoDr_lt_one_sub {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    initExpRhoDr g < 1 - g := by
  rw [initExpRhoDr_eq]
  linarith only [hg.2]

/-- The logarithmic scale separation forces a positive integer shift. -/
theorem shift_pos_of_scale_separation {C K : ℝ} {l : ℤ} (hC : 0 < C)
    (hK : 1 ≤ K) (hsep : C * (1 + Real.log K) ≤ (l : ℝ)) : 0 < l := by
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hprod : 0 < C * (1 + Real.log K) :=
    mul_pos hC (by linarith only [hlog])
  exact_mod_cast hprod.trans_le hsep

end

end Bridge
end HighContrast
end Homogenization
