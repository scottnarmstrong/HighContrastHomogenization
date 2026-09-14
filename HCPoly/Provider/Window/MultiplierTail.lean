/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.SuccessorTail
import HCPoly.Provider.Window.StoppedScale

namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem sourceRemainderScale_pos (d : ℕ) (jStar : ℤ) (K : ℝ) :
    0 < sourceRemainderScale d jStar K := by
  rw [sourceRemainderScale]
  exact mul_pos (pow_pos (by rw [growthBar]; norm_num) _)
    (zpow_pos (by norm_num) _)

private theorem multiplier_sub_one_le_pow_offset {g : ℝ} (hg : g ≤ 1)
    (E : BlockMat d) (jStar M : ℤ) (a : CoeffSpace d) :
    windowMultiplier g E jStar M a - 1 ≤
      (3 : ℝ) ^ windowScaleOffset g E jStar M a := by
  have hexp :
      g * (windowScaleOffset g E jStar M a : ℝ) ≤
        (windowScaleOffset g E jStar M a : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg _)
  calc
    windowMultiplier g E jStar M a - 1 ≤
        windowMultiplier g E jStar M a := sub_le_self _ zero_le_one
    _ ≤ (3 : ℝ) ^ (windowScaleOffset g E jStar M a : ℝ) := by
      rw [windowMultiplier]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (3 : ℝ) ^ windowScaleOffset g E jStar M a :=
      Real.rpow_natCast 3 _

private theorem source_tail_argument_lt_predecessor {g : ℝ}
    (E : BlockMat d) (jStar M : ℤ) (a : CoeffSpace d) (K t : ℝ)
    (hoff : 0 < windowScaleOffset g E jStar M a)
    (hbound : sourceRemainderScale d jStar K * t <
      (3 : ℝ) ^ windowScaleOffset g E jStar M a) :
    t * growthBar K ^ (4 * (d + 1)) *
          (3 : ℝ) ^ (M - jStar + 1) <
      (3 : ℝ) ^
        (M + ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ)) := by
  have hfac : 0 < (3 : ℝ) ^ (M - 1) := by positivity
  have hmul := mul_lt_mul_of_pos_right hbound hfac
  rw [sourceRemainderScale] at hmul
  calc
    t * growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ (M - jStar + 1) =
        (growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ (2 - jStar) * t) *
          (3 : ℝ) ^ (M - 1) := by
            rw [show M - jStar + 1 = (2 - jStar) + (M - 1) by omega,
              zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
            ring
    _ < (3 : ℝ) ^ windowScaleOffset g E jStar M a *
          (3 : ℝ) ^ (M - 1) := hmul
    _ = (3 : ℝ) ^
          (M + ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      omega

private theorem multiplier_tail_event_subset_successor_tail {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (E : BlockMat d) (jStar M : ℤ)
    (K t : ℝ) (ht : 1 ≤ t) :
    IndependentSums.upperTailEvent
        (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
        (sourceRemainderScale d jStar K * t) ⊆
      {a : CoeffSpace d |
        ENNReal.ofReal
          (max ((3 : ℝ) ^ M)
            (t * growthBar K ^ (4 * (d + 1)) *
              (3 : ℝ) ^ (M - jStar + 1))) <
          successorScale g E (M - jStar) a} := by
  intro a ha
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hscale : 0 < sourceRemainderScale d jStar K :=
    sourceRemainderScale_pos d jStar K
  have hoff : 0 < windowScaleOffset g E jStar M a := by
    by_contra hnot
    have hoffzero : windowScaleOffset g E jStar M a = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero : windowMultiplier g E jStar M a - 1 = 0 := by
      simp [windowMultiplier, hoffzero]
    rw [IndependentSums.upperTailEvent, Set.mem_ofPred_eq, hzero] at ha
    have hpositive : 0 < sourceRemainderScale d jStar K * t :=
      mul_pos hscale htpos
    exact (not_lt_of_ge hpositive.le) ha
  have hbound : sourceRemainderScale d jStar K * t <
      (3 : ℝ) ^ windowScaleOffset g E jStar M a :=
    ha.trans_le (multiplier_sub_one_le_pow_offset hg.2.le E jStar M a)
  have harg := source_tail_argument_lt_predecessor E jStar M a K t hoff hbound
  have hbase : (3 : ℝ) ^ M ≤
      (3 : ℝ) ^
        (M + ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    have hnonneg : (0 : ℤ) ≤
        ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ) := by
      exact_mod_cast (Nat.zero_le (windowScaleOffset g E jStar M a - 1))
    exact le_add_of_nonneg_right hnonneg
  have hmax : max ((3 : ℝ) ^ M)
      (t * growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ (M - jStar + 1)) ≤
      (3 : ℝ) ^
        (M + ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ)) :=
    max_le hbase harg.le
  change ENNReal.ofReal
      (max ((3 : ℝ) ^ M)
        (t * growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ (M - jStar + 1))) <
      successorScale g E (M - jStar) a
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmax)
    (stoppedThreshold_lt_successorScale hoff)

/-! The stopped multiplier has the ordinary source-gauge tail at the exact
source-remainder scale. -/
theorem windowMultiplier_isBigOWith [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {jStar M : ℤ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M) :
    IndependentSums.IsBigOWith P Ψ
      (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
      (sourceRemainderScale d jStar K) := by
  intro t ht
  have hsub := multiplier_tail_event_subset_successor_tail
    hg E jStar M K t ht
  calc
    P.real (IndependentSums.upperTailEvent
        (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
        (sourceRemainderScale d jStar K * t)) ≤
        P.real {a : CoeffSpace d |
          ENNReal.ofReal
            (max ((3 : ℝ) ^ M)
              (t * growthBar K ^ (4 * (d + 1)) *
                (3 : ℝ) ^ (M - jStar + 1))) <
            successorScale g E (M - jStar) a} := measureReal_mono hsub
    _ ≤ (Ψ t)⁻¹ := measureReal_successorScale_tail hstat hdag hQ hw ht

end
end Window
end HighContrast
end Homogenization
