/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ShiftedDriftReduction

/-!
# Summed normalization change for shifted drift

The lower comparison changes the terminal inverse only after the complete old
terminal-gap row has been summed.  This form therefore requires nonnegativity
only of the final scalar majorant, not of every cross-grid gap.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- A summed old-terminal gap bound may be transported to the new terminal
normalization with the same factor two and dimensional slack. -/
theorem weighted_terminal_gaps_le_of_sum_bound
    {rho eta R : ℝ} {b n : ℤ} (A B : FullBlockMat d)
    (hA : A.PosDef) (hB : B.PosDef) (heta0 : 0 ≤ eta)
    (heta4 : eta ≤ 1 / 4) (hBA : (1 - eta) • B ≤ A)
    (F : ℤ → FullBlockMat d)
    (hF : ∀ j ∈ Finset.Ico b n, (F j).PosSemidef)
    (hR0 : 0 ≤ R)
    (hR : ∑ j ∈ Finset.Ico b n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          Matrix.trace (B⁻¹ * (F j - B)) ≤ R) :
    ∑ j ∈ Finset.Ico b n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          Matrix.trace (A⁻¹ * (F j - A)) ≤
      2 * R + 4 * (d : ℝ) * eta *
        ∑ j ∈ Finset.Ico b n,
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) := by
  have heta1 : eta < 1 := by
    norm_num at heta4 ⊢
    linarith only [heta4]
  have hden : 0 < 1 - eta := sub_pos.mpr heta1
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := inv_nonneg.mpr hden.le
  have hinv2 : (1 - eta)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith only [heta4]
  have hetaerr : 2 * (d : ℝ) * eta / (1 - eta) ≤
      4 * (d : ℝ) * eta := by
    have hdeta : 0 ≤ 2 * (d : ℝ) * eta := by positivity
    rw [div_eq_mul_inv]
    have h := mul_le_mul_of_nonneg_left hinv2 hdeta
    nlinarith only [h]
  have hpoint : ∀ j ∈ Finset.Ico b n,
      Matrix.trace (A⁻¹ * (F j - A)) ≤
        (1 - eta)⁻¹ * Matrix.trace (B⁻¹ * (F j - B)) +
          4 * (d : ℝ) * eta := by
    intro j hj
    exact (fullBlock_trace_inv_mul_sub_le_of_smul_le hA hB (hF j hj)
      heta1 hBA).trans (add_le_add_right hetaerr _)
  have hsum :
      ∑ j ∈ Finset.Ico b n,
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
            Matrix.trace (A⁻¹ * (F j - A)) ≤
        (1 - eta)⁻¹ *
            ∑ j ∈ Finset.Ico b n,
              (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
                Matrix.trace (B⁻¹ * (F j - B)) +
          4 * (d : ℝ) * eta *
            ∑ j ∈ Finset.Ico b n,
              (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico b n,
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
            ((1 - eta)⁻¹ * Matrix.trace (B⁻¹ * (F j - B)) +
              4 * (d : ℝ) * eta) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (hpoint j hj) (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
  have hfirst : (1 - eta)⁻¹ *
      ∑ j ∈ Finset.Ico b n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          Matrix.trace (B⁻¹ * (F j - B)) ≤ (1 - eta)⁻¹ * R :=
    mul_le_mul_of_nonneg_left hR hinv0
  have htwo : (1 - eta)⁻¹ * R ≤ 2 * R := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hinv2 hR0
  exact hsum.trans (add_le_add_left (hfirst.trans htwo) _)

end

end Bridge
end HighContrast
end Homogenization
