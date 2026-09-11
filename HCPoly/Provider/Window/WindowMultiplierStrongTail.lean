/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.SharperContinuousTail
import HCPoly.Provider.Window.MultiplierTail


namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem sourceRemainderScale_pos_strong (d : ℕ) (jStar : ℤ) (K : ℝ) :
    0 < sourceRemainderScale d jStar K := by
  rw [sourceRemainderScale]
  exact mul_pos (pow_pos (by rw [growthBar]; norm_num) _)
    (zpow_pos (by norm_num) _)

private theorem multiplier_sub_one_le_pow_offset_strong {g : ℝ} (hg : g ≤ 1)
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

private theorem source_tail_argument_lt_predecessor_strong {g : ℝ}
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

private theorem multiplier_tail_event_subset_successor_tail_strong {g : ℝ}
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
    sourceRemainderScale_pos_strong d jStar K
  have hoff : 0 < windowScaleOffset g E jStar M a := by
    by_contra hnot
    have hoffzero : windowScaleOffset g E jStar M a = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero : windowMultiplier g E jStar M a - 1 = 0 := by
      simp [windowMultiplier, hoffzero]
    rw [IndependentSums.upperTailEvent, Set.mem_setOf_eq, hzero] at ha
    exact (not_lt_of_ge (mul_pos hscale htpos).le) ha
  have hbound : sourceRemainderScale d jStar K * t <
      (3 : ℝ) ^ windowScaleOffset g E jStar M a :=
    ha.trans_le (multiplier_sub_one_le_pow_offset_strong hg.2.le E jStar M a)
  have harg := source_tail_argument_lt_predecessor_strong E jStar M a K t hoff hbound
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
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmax)
    (stoppedThreshold_lt_successorScale hoff)

/-- The stopped excess retains the extra inverse power in its tail. -/
theorem windowMultiplier_sub_one_strong_tail [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {jStar M : ℤ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {t : ℝ} (ht : 1 ≤ t) :
    P.real (IndependentSums.upperTailEvent
        (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
        (sourceRemainderScale d jStar K * t)) ≤
      (t * Ψ t)⁻¹ := by
  let C : ℝ := growthBar K ^ (4 * (d + 1))
  have hB : 2 ≤ growthBar K := by rw [growthBar]; exact le_max_left _ _
  have hB1 : 1 ≤ growthBar K := one_le_two.trans hB
  have hexp : 1 ≤ 4 * (d + 1) := by omega
  have hBC : growthBar K ≤ C := by
    simpa only [C, pow_one] using
      (pow_le_pow_right₀ hB1 hexp : growthBar K ^ 1 ≤ growthBar K ^ (4 * (d + 1)))
  have hcoef : (3 / (2 * C) : ℝ) ≤ 1 := by
    have hthree : (3 / 2 : ℝ) ≤ C := (by norm_num : (3 / 2 : ℝ) ≤ 2).trans (hB.trans hBC)
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_two (hB.trans hBC)
    rw [div_le_one (by positivity : 0 < 2 * C)]
    linarith only [hthree]
  have hinv : 0 ≤ (t * Ψ t)⁻¹ := by
    have hψ : 0 ≤ Ψ t := zero_le_one.trans
      (hdag.gauge_admissible.2 (zero_le_one.trans ht))
    exact inv_nonneg.mpr (mul_nonneg (zero_le_one.trans ht) hψ)
  have hsub := multiplier_tail_event_subset_successor_tail_strong
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
    _ ≤ (3 / (2 * C) : ℝ) * (t * Ψ t)⁻¹ := by
      simpa only [C] using
        measureReal_successorScale_tail_sharp hstat hdag hQ hw ht
    _ ≤ 1 * (t * Ψ t)⁻¹ := mul_le_mul_of_nonneg_right hcoef hinv
    _ = (t * Ψ t)⁻¹ := one_mul _

/-- The normalized stopped excess has tail `(t Ψ(t))⁻¹` above one. -/
theorem normalized_windowMultiplier_sub_one_strong_tail [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {jStar M : ℤ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {t : ℝ} (ht : 1 ≤ t) :
    P.real {a : CoeffSpace d | t <
        (windowMultiplier g E jStar M a - 1) /
          sourceRemainderScale d jStar K} ≤ (t * Ψ t)⁻¹ := by
  have hscale : 0 < sourceRemainderScale d jStar K :=
    sourceRemainderScale_pos_strong d jStar K
  have hset : {a : CoeffSpace d | t <
        (windowMultiplier g E jStar M a - 1) /
          sourceRemainderScale d jStar K} =
      IndependentSums.upperTailEvent
        (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
        (sourceRemainderScale d jStar K * t) := by
    ext a
    change (t < (windowMultiplier g E jStar M a - 1) /
      sourceRemainderScale d jStar K) ↔
      sourceRemainderScale d jStar K * t < windowMultiplier g E jStar M a - 1
    rw [lt_div_iff₀ hscale]
    ring_nf
  rw [hset]
  exact windowMultiplier_sub_one_strong_tail hstat hdag hg hQ hw ht

end
end Window
end HighContrast
end Homogenization

