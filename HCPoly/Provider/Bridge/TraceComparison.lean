/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.DeterminantLoss
import HCPoly.Provider.PortableHistory.TraceGap

/-!
# The shifted-drift comparison error

This file proves the trace inequality which changes the terminal normalization
in the shifted determinant drift.  Its dimension term is explicit because the
bridge applies it to a doubled block.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open scoped MatrixOrder Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem comparison_error_scalar_identity (eta x m : ℝ) (heta : eta ≠ 1) :
    (1 - eta)⁻¹ * (x - m) + m * eta / (1 - eta) =
      (1 - eta)⁻¹ * x - m := by
  have hden : 1 - eta ≠ 0 := sub_ne_zero.mpr (Ne.symm heta)
  field_simp [hden]
  ring

/-- If `A` dominates `(1-η)B`, changing the inverse normalization from `A`
to `B` costs the printed dimensional error. -/
theorem trace_inv_mul_sub_le_of_smul_le {A B X : Matrix n n ℝ} (hA : A.PosDef)
    (hB : B.PosDef) (hX : X.PosSemidef) {eta : ℝ} (heta₁ : eta < 1)
    (hBA : (1 - eta) • B ≤ A) :
    Matrix.trace (A⁻¹ * (X - A)) ≤
      (1 - eta)⁻¹ * Matrix.trace (B⁻¹ * (X - B)) +
        (Fintype.card n : ℝ) * eta / (1 - eta) := by
  have hc : 0 < 1 - eta := sub_pos.mpr heta₁
  have hcB : ((1 - eta) • B).PosDef := posDef_smul hB hc
  have hinv : A⁻¹ ≤ (1 - eta)⁻¹ • B⁻¹ := by
    have h := inv_le_inv_of_le hcB hA hBA
    rw [inv_smul_of_isUnit hc.ne' (isUnit_det_of_posDef hB)] at h
    exact h
  have htrace : Matrix.trace (A⁻¹ * X) ≤
      (1 - eta)⁻¹ * Matrix.trace (B⁻¹ * X) := by
    have h := PortableHistory.trace_mul_le_trace_mul hX hinv
    calc
      Matrix.trace (A⁻¹ * X) = Matrix.trace (X * A⁻¹) := Matrix.trace_mul_comm _ _
      _ ≤ Matrix.trace (X * ((1 - eta)⁻¹ • B⁻¹)) := h
      _ = (1 - eta)⁻¹ * Matrix.trace (B⁻¹ * X) := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
          Matrix.trace_mul_comm X B⁻¹]
  have hcard : Matrix.trace (1 : Matrix n n ℝ) = (Fintype.card n : ℝ) :=
    Matrix.trace_one
  have hAunit : IsUnit A.det := isUnit_det_of_posDef hA
  have hBunit : IsUnit B.det := isUnit_det_of_posDef hB
  calc
    Matrix.trace (A⁻¹ * (X - A)) =
        Matrix.trace (A⁻¹ * X) - (Fintype.card n : ℝ) := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul _ hAunit, hcard]
    _ ≤ (1 - eta)⁻¹ * Matrix.trace (B⁻¹ * X) -
        (Fintype.card n : ℝ) := sub_le_sub_right htrace _
    _ = (1 - eta)⁻¹ *
          (Matrix.trace (B⁻¹ * X) - (Fintype.card n : ℝ)) +
        (Fintype.card n : ℝ) * eta / (1 - eta) := by
      rw [comparison_error_scalar_identity eta
        (Matrix.trace (B⁻¹ * X)) (Fintype.card n : ℝ) (ne_of_lt heta₁)]
    _ = (1 - eta)⁻¹ * Matrix.trace (B⁻¹ * (X - B)) +
        (Fintype.card n : ℝ) * eta / (1 - eta) := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul _ hBunit, hcard]

/-- The normalization-change error on the doubled block has dimension `2d`. -/
theorem fullBlock_trace_inv_mul_sub_le_of_smul_le {d : ℕ}
    {A B X : FullBlockMat d} (hA : A.PosDef) (hB : B.PosDef)
    (hX : X.PosSemidef) {eta : ℝ} (heta₁ : eta < 1)
    (hBA : (1 - eta) • B ≤ A) :
    Matrix.trace (A⁻¹ * (X - A)) ≤
      (1 - eta)⁻¹ * Matrix.trace (B⁻¹ * (X - B)) +
        2 * (d : ℝ) * eta / (1 - eta) := by
  have h := trace_inv_mul_sub_le_of_smul_le hA hB hX heta₁ hBA
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  rwa [hcard] at h

end

end Bridge
end HighContrast
end Homogenization
