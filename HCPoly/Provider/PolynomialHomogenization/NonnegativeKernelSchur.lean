/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Schur test for nonnegative kernels

This file gives the squared `L²` form of the Schur test for an
extended-nonnegative-real-valued kernel. The formulation uses Lebesgue
integrals throughout, so Tonelli's theorem handles kernels and functions that
are not known a priori to be integrable.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem lintegral_mul_rpow_two_le
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    {w f : β → ℝ≥0∞} (hw : AEMeasurable w ν) (hf : AEMeasurable f ν) :
    (∫⁻ y, w y * f y ∂ν) ^ (2 : ℝ) ≤
      (∫⁻ y, w y ∂ν) * ∫⁻ y, w y * f y ^ (2 : ℝ) ∂ν := by
  have hwf : AEMeasurable (fun y => w y * f y ^ (2 : ℝ)) ν :=
    hw.mul (hf.pow_const (2 : ℝ))
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    (μ := ν) (f := w) (g := fun y => w y * f y ^ (2 : ℝ))
    hw hwf (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hleft :
      (∫⁻ y, w y ^ (1 / 2 : ℝ) *
          (w y * f y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ∂ν) =
        ∫⁻ y, w y * f y ∂ν := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
        (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hholder
  have hsquare := ENNReal.rpow_le_rpow hholder (by norm_num : 0 ≤ (2 : ℝ))
  calc
    (∫⁻ y, w y * f y ∂ν) ^ (2 : ℝ)
        ≤ ((∫⁻ y, w y ∂ν) ^ (1 / 2 : ℝ) *
            (∫⁻ y, w y * f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
      hsquare
    _ = (∫⁻ y, w y ∂ν) * ∫⁻ y, w y * f y ^ (2 : ℝ) ∂ν := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

end

end HighContrast
end Homogenization
