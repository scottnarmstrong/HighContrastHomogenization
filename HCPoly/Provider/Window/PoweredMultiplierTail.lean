/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.MultiplierTail

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

private theorem poweredRemainderScale_eq_rpow_source
    (d : ℕ) (jStar : ℤ) (g K : ℝ) :
    poweredRemainderScale d jStar g K =
      (sourceRemainderScale d jStar K) ^ g := by
  have hB : 0 ≤ growthBar K := by rw [growthBar]; positivity
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hBexp : 4 * g * ((d : ℝ) + 1) =
      (((4 * (d + 1) : ℕ) : ℝ) * g) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring
  have h3exp : g * (2 - (jStar : ℝ)) =
      ((((2 : ℤ) - jStar : ℤ) : ℝ) * g) := by
    norm_num only [Int.cast_sub, Int.cast_ofNat]
    ring
  calc
    poweredRemainderScale d jStar g K =
        growthBar K ^ (((4 * (d + 1) : ℕ) : ℝ) * g) *
          (3 : ℝ) ^ ((((2 : ℤ) - jStar : ℤ) : ℝ) * g) := by
      rw [poweredRemainderScale, hBexp, h3exp]
    _ = (growthBar K ^ (4 * (d + 1))) ^ g *
          ((3 : ℝ) ^ ((2 : ℤ) - jStar)) ^ g := by
      rw [Real.rpow_mul hB, Real.rpow_natCast,
        Real.rpow_mul h3, Real.rpow_intCast]
    _ = (growthBar K ^ (4 * (d + 1)) *
          (3 : ℝ) ^ ((2 : ℤ) - jStar)) ^ g := by
      rw [Real.mul_rpow (pow_nonneg hB _) (zpow_nonneg h3 _)]
    _ = (sourceRemainderScale d jStar K) ^ g := by
      rw [sourceRemainderScale]

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

private theorem powered_tail_event_subset_successor_tail {g : ℝ}
    (hg0 : 0 < g) (E : BlockMat d) (jStar M : ℤ) (K t : ℝ) (ht : 1 ≤ t) :
    IndependentSums.upperTailEvent
        (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
        (poweredRemainderScale d jStar g K * t) ⊆
      {a : CoeffSpace d |
        ENNReal.ofReal
          (max ((3 : ℝ) ^ M)
            (t ^ g⁻¹ * growthBar K ^ (4 * (d + 1)) *
              (3 : ℝ) ^ (M - jStar + 1))) <
          successorScale g E (M - jStar) a} := by
  intro a ha
  let u : ℝ := t ^ g⁻¹
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hu : 1 ≤ u := by
    dsimp only [u]
    exact Real.one_le_rpow ht (inv_nonneg.mpr hg0.le)
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hscale : 0 < sourceRemainderScale d jStar K :=
    sourceRemainderScale_pos d jStar K
  have hpowered : 0 < poweredRemainderScale d jStar g K := by
    rw [poweredRemainderScale_eq_rpow_source]
    exact Real.rpow_pos_of_pos hscale g
  have hoff : 0 < windowScaleOffset g E jStar M a := by
    by_contra hnot
    have hoffzero : windowScaleOffset g E jStar M a = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero : windowMultiplier g E jStar M a - 1 = 0 := by
      simp [windowMultiplier, hoffzero]
    rw [IndependentSums.upperTailEvent, Set.mem_ofPred_eq, hzero] at ha
    exact (not_lt_of_ge (mul_pos hpowered htpos).le) ha
  have hpbound : poweredRemainderScale d jStar g K * t <
      (3 : ℝ) ^ (g * (windowScaleOffset g E jStar M a : ℝ)) := by
    calc
      poweredRemainderScale d jStar g K * t <
          windowMultiplier g E jStar M a - 1 := ha
      _ ≤ windowMultiplier g E jStar M a := sub_le_self _ zero_le_one
      _ = (3 : ℝ) ^ (g * (windowScaleOffset g E jStar M a : ℝ)) := rfl
  have hsource : sourceRemainderScale d jStar K * u <
      (3 : ℝ) ^ windowScaleOffset g E jStar M a := by
    apply (Real.rpow_lt_rpow_iff
      (mul_nonneg hscale.le hu0)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      hg0).mp
    calc
      (sourceRemainderScale d jStar K * u) ^ g =
          poweredRemainderScale d jStar g K * t := by
        rw [Real.mul_rpow hscale.le hu0, ← poweredRemainderScale_eq_rpow_source]
        dsimp only [u]
        rw [Real.rpow_inv_rpow htpos.le hg0.ne']
      _ < ((3 : ℝ) ^ windowScaleOffset g E jStar M a) ^ g := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        rw [mul_comm (windowScaleOffset g E jStar M a : ℝ) g]
        exact hpbound
  have harg := source_tail_argument_lt_predecessor E jStar M a K u hoff hsource
  have hbase : (3 : ℝ) ^ M ≤
      (3 : ℝ) ^
        (M + ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    have hnonneg : (0 : ℤ) ≤
        ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ) := by
      exact_mod_cast (Nat.zero_le (windowScaleOffset g E jStar M a - 1))
    exact le_add_of_nonneg_right hnonneg
  have hmax : max ((3 : ℝ) ^ M)
      (u * growthBar K ^ (4 * (d + 1)) * (3 : ℝ) ^ (M - jStar + 1)) ≤
      (3 : ℝ) ^
        (M + ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ)) :=
    max_le hbase harg.le
  change ENNReal.ofReal
      (max ((3 : ℝ) ^ M)
        (t ^ g⁻¹ * growthBar K ^ (4 * (d + 1)) *
          (3 : ℝ) ^ (M - jStar + 1))) <
      successorScale g E (M - jStar) a
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by simpa only [u] using hmax))
    (stoppedThreshold_lt_successorScale hoff)

/-- The stopped multiplier has the powered source-gauge tail at the exact
powered remainder scale. -/
theorem windowMultiplier_isBigOWith_powered [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hg0 : 0 < g) {jStar M : ℤ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M) :
    IndependentSums.IsBigOWith P (poweredGauge Ψ g)
      (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
      (poweredRemainderScale d jStar g K) := by
  intro t ht
  have hsub := powered_tail_event_subset_successor_tail
    hg0 E jStar M K t ht
  calc
    P.real (IndependentSums.upperTailEvent
        (fun a : CoeffSpace d => windowMultiplier g E jStar M a - 1)
        (poweredRemainderScale d jStar g K * t)) ≤
        P.real {a : CoeffSpace d |
          ENNReal.ofReal
            (max ((3 : ℝ) ^ M)
              (t ^ g⁻¹ * growthBar K ^ (4 * (d + 1)) *
                (3 : ℝ) ^ (M - jStar + 1))) <
            successorScale g E (M - jStar) a} := measureReal_mono hsub
    _ ≤ (Ψ (t ^ g⁻¹))⁻¹ :=
      measureReal_successorScale_tail hstat hdag hQ hw
        (Real.one_le_rpow ht (inv_nonneg.mpr hg0.le))
    _ = (poweredGauge Ψ g t)⁻¹ := rfl

end
end Window
end HighContrast
end Homogenization
