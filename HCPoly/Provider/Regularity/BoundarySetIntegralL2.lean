/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Homogenization.Multiscale.NormalizedNorms

/-!
# Normalized boundary-set integral bound

This file isolates the analytic estimate used to compare averages on a cube
and on a fixed translate.  Cauchy--Schwarz bounds the integral over the lost
boundary set by the full normalized `L²` norm times the square root of the
lost normalized volume.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory Set

noncomputable section

/-- The integral of an `L²` vector field over a measurable part of a
normalized cube is controlled by its full normalized `L²` norm and the
square root of the normalized volume of that part. -/
theorem norm_setIntegral_normalizedCubeMeasure_le_cubeLpNorm_mul_sqrt_measure
    {d : ℕ} (Q : TriadicCube d) {S : Set (Vec d)}
    (hS : MeasurableSet S) (F : Vec d → Vec d)
    (hF : MemLp F (2 : ENNReal) (normalizedCubeMeasure Q)) :
    ‖∫ x in S, F x ∂normalizedCubeMeasure Q‖ ≤
      cubeLpNorm Q (2 : ENNReal) F *
        Real.sqrt ((normalizedCubeMeasure Q).real S) := by
  let μ : Measure (Vec d) := normalizedCubeMeasure Q
  let g : Vec d → ℝ := S.indicator (fun _ ↦ 1)
  have hg : MemLp g (2 : ENNReal) μ := by
    exact memLp_indicator_const (2 : ENNReal) hS 1
      (Or.inr (measure_lt_top μ S).ne)
  have hFnorm : MemLp (fun x ↦ ‖F x‖) (2 : ENNReal) μ := by
    exact hF.norm
  have hnonnegF : 0 ≤ᵐ[μ] fun x ↦ ‖F x‖ :=
    Filter.Eventually.of_forall fun x ↦ norm_nonneg (F x)
  have hnonnegG : 0 ≤ᵐ[μ] g := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ S <;> simp [g, hx]
  have hproduct :
      ∫ x in S, ‖F x‖ ∂μ = ∫ x, ‖F x‖ * g x ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ S <;> simp [g, hx]
  have hholder :
      ∫ x, ‖F x‖ * g x ∂μ ≤
        (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    apply integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two hnonnegF hnonnegG
    · simpa using hFnorm
    · simpa using hg
  have hFfactor :
      (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        cubeLpNorm Q (2 : ENNReal) F := by
    have hsq := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
      (Q := Q) (p := (2 : ENNReal)) (f := F)
      (by norm_num) (by simp) hF
    have hsq' :
        (cubeLpNorm Q (2 : ENNReal) F) ^ (2 : ℝ) =
          ∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ := by
      simpa [μ, cubeAverage_eq_integral_normalizedCubeMeasure] using hsq
    have hsqrt :
        (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
          Real.sqrt (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) := by
      simpa [one_div] using
        (Real.sqrt_eq_rpow (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ)).symm
    rw [hsqrt]
    rw [← hsq']
    simpa only [Real.rpow_two] using
      Real.sqrt_sq_eq_abs (cubeLpNorm Q (2 : ENNReal) F)
        |>.trans (abs_of_nonneg (cubeLpNorm_nonneg Q (2 : ENNReal) F))
  have hGsq :
      ∫ x, g x ^ (2 : ℝ) ∂μ = μ.real S := by
    rw [← integral_indicator_one hS]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ S <;> simp [g, hx]
  have hGfactor :
      (∫ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        Real.sqrt (μ.real S) := by
    rw [hGsq]
    simpa [one_div] using (Real.sqrt_eq_rpow (μ.real S)).symm
  calc
    ‖∫ x in S, F x ∂normalizedCubeMeasure Q‖
        ≤ ∫ x in S, ‖F x‖ ∂normalizedCubeMeasure Q :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖F x‖ * g x ∂μ := hproduct
    _ ≤ (∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ = cubeLpNorm Q (2 : ENNReal) F * Real.sqrt (μ.real S) := by
      rw [hFfactor, hGfactor]
    _ = cubeLpNorm Q (2 : ENNReal) F *
          Real.sqrt ((normalizedCubeMeasure Q).real S) := rfl

end

end HighContrast
end Homogenization
