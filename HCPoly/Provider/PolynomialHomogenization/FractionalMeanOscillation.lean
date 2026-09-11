/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.EuclideanAmbient
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Fractional mean oscillation on a bounded set

Pairwise differences control the squared deviation from the volume average.
On a set of bounded Euclidean diameter, inserting the fractional kernel gives
the corresponding fractional Poincare estimate.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private noncomputable def normalizedDomainMeasure (U : Set (Vec d)) :
    Measure (Vec d) :=
  (volume U)⁻¹ • volume.restrict U

private theorem eLpNorm_two_eq_rpow {A : Type*} [MeasurableSpace A]
    {E : Type*} [NormedAddCommGroup E] (f : A → E) (mu : Measure A) :
    eLpNorm f 2 mu = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  norm_num

private theorem enorm_sub_integral_rpow_two_le
    {A : Type*} [MeasurableSpace A]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure A) [IsProbabilityMeasure mu]
    {f : A → E} (hf : Integrable f mu) (x : A) :
    ‖f x - ∫ y, f y ∂mu‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂mu := by
  have hgm : AEStronglyMeasurable (fun y => f x - f y) mu :=
    aestronglyMeasurable_const.sub hf.aestronglyMeasurable
  have hint : ∫ y, (f x - f y) ∂mu = f x - ∫ y, f y ∂mu := by
    rw [integral_sub (integrable_const _) hf, integral_const]
    simp
  have hL1 : ‖f x - ∫ y, f y ∂mu‖ₑ ≤ ∫⁻ y, ‖f x - f y‖ₑ ∂mu := by
    rw [← hint]
    exact enorm_integral_le_lintegral_enorm _
  have hL2 : (∫⁻ y, ‖f x - f y‖ₑ ∂mu) ≤
      (∫⁻ y, ‖f x - f y‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    have hcmp := eLpNorm_le_eLpNorm_of_exponent_le
      (μ := mu) (p := 1) (q := 2) (f := fun y => f x - f y)
      (by norm_num) hgm
    rwa [eLpNorm_one_eq_lintegral_enorm, eLpNorm_two_eq_rpow] at hcmp
  have hpow := ENNReal.rpow_le_rpow (hL1.trans hL2) (by norm_num : (0 : ℝ) ≤ 2)
  refine hpow.trans (le_of_eq ?_)
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem integral_normalizedDomainMeasure_eq_volumeAverageVec
    {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict U)) :
    ∫ x, F x ∂normalizedDomainMeasure U = volumeAverageVec U F := by
  funext i
  have hproj : ∫ x in U, F x i ∂volume = (∫ x in U, F x ∂volume) i := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).integral_comp_comm hF
  rw [normalizedDomainMeasure, integral_smul_measure, volumeAverageVec, volumeAverage,
    Pi.smul_apply, smul_eq_mul, ENNReal.toReal_inv, hproj]

private theorem enorm_hilbertVec_sq (v : Vec d) :
    ‖HilbertVec.ofVec v‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (vecNormSq v) := by
  rw [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  simpa [vecNormSq, vecDot, HilbertVec.ofVec, PiLp.toLp_apply, pow_two] using
    HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec v)

private theorem enorm_hilbertVec_sub_sq (v w : Vec d) :
    ‖HilbertVec.ofVec v - HilbertVec.ofVec w‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal (vecNormSq (v - w)) := by
  have hsub : HilbertVec.ofVec v - HilbertVec.ofVec w = HilbertVec.ofVec (v - w) := by
    exact ((HilbertVec.ofVecL d).map_sub v w).symm
  rw [hsub, enorm_hilbertVec_sq]

end

end HighContrast
end Homogenization
