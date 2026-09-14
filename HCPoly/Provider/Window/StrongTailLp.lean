/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.StrongTailMoment

namespace Homogenization
namespace IndependentSums

open MeasureTheory Set _root_.Filter
open scoped ENNReal BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem eLpNorm_le_integer_of_strongPsiTail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {B : ℝ} {W : Ω → ℝ} (N : ℕ)
    (hN : 1 ≤ N) (hB : 2 ≤ B) (hGrowth : HasPsiGrowth Ψ B)
    (hAdmissible : AdmissiblePsi Ψ) (hWm : AEMeasurable W μ)
    (hW0 : ∀ ω, 0 ≤ W ω)
    (htail : ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real {ω | t < W ω} ≤ (t * Ψ t)⁻¹) :
    eLpNorm W (ENNReal.ofReal (N : ℝ)) μ ≤
      ENNReal.ofReal
        ((1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ natTriangular N) ^
          ((N : ℝ)⁻¹)) := by
  let D : ℝ := 1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ natTriangular N
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hD0 : 0 ≤ D := by
    have hlog : 0 ≤ Real.log B := Real.log_nonneg (one_le_two.trans hB)
    dsimp only [D]
    positivity
  have hlin : ∫⁻ ω, ENNReal.ofReal (W ω ^ (N : ℝ)) ∂μ ≤ ENNReal.ofReal D := by
    simpa only [D] using lintegral_rpow_le_of_strongPsiTail
      N hN hB hGrowth hAdmissible hWm hW0 htail
  have hq0 : ENNReal.ofReal (N : ℝ) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hNpos
  have hqtop : ENNReal.ofReal (N : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqreal : (ENNReal.ofReal (N : ℝ)).toReal = (N : ℝ) :=
    ENNReal.toReal_ofReal hNpos.le
  have hint : ∫⁻ ω, ‖W ω‖ₑ ^ (N : ℝ) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (W ω ^ (N : ℝ)) ∂μ := by
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal (hW0 ω),
      ENNReal.ofReal_rpow_of_nonneg (hW0 ω) hNpos.le]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop, hqreal, hint, one_div]
  calc
    (∫⁻ ω, ENNReal.ofReal (W ω ^ (N : ℝ)) ∂μ) ^ ((N : ℝ)⁻¹) ≤
        (ENNReal.ofReal D) ^ ((N : ℝ)⁻¹) :=
      ENNReal.rpow_le_rpow hlin (inv_nonneg.mpr hNpos.le)
    _ = ENNReal.ofReal (D ^ ((N : ℝ)⁻¹)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hD0 (inv_nonneg.mpr hNpos.le)]
    _ = ENNReal.ofReal
        ((1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ natTriangular N) ^
          ((N : ℝ)⁻¹)) := by rfl

/-- A tail bounded by `(t Ψ(t))⁻¹` satisfies the printed all-real moment
multiplier estimate. -/
theorem eLpNorm_le_of_strongPsiTail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {B : ℝ} {W : Ω → ℝ}
    (hB : 2 ≤ B) (hGrowth : HasPsiGrowth Ψ B)
    (hAdmissible : AdmissiblePsi Ψ) (hWm : AEMeasurable W μ)
    (hW0 : ∀ ω, 0 ≤ W ω)
    (htail : ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real {ω | t < W ω} ≤ (t * Ψ t)⁻¹)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm W (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal
        ((1 + 2 * p * B ^ (⌈p * (p + 1) / 2⌉ : ℤ) * (1 + Real.log B)) ^
          (1 / p)) := by
  let N : ℕ := Nat.ceil p
  let T : ℕ := natTriangular N
  let q : ℤ := ⌈p * (p + 1) / 2⌉
  let DN : ℝ := 1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ T
  let Dp : ℝ := 1 + 2 * p * B ^ q * (1 + Real.log B)
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpN : p ≤ (N : ℝ) := by exact Nat.le_ceil p
  have hNlt : (N : ℝ) < p + 1 := by
    exact Nat.ceil_lt_add_one hp0.le
  have hN : 1 ≤ N := by exact_mod_cast hp.trans hpN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNm1 : (N : ℝ) - 1 < p := by linarith only [hNlt]
  have hN2p : (N : ℝ) ≤ 2 * p := by
    have hpone : p + 1 ≤ 2 * p := by linarith only [hp]
    exact hNlt.le.trans hpone
  have hTlt : (T : ℝ) < p * (p + 1) / 2 := by
    have hprod : (N : ℝ) * ((N : ℝ) - 1) < p * (p + 1) := by
      calc
        (N : ℝ) * ((N : ℝ) - 1) < (N : ℝ) * p :=
          mul_lt_mul_of_pos_left hNm1 hNpos
        _ ≤ (p + 1) * p := mul_le_mul_of_nonneg_right hNlt.le hp0.le
        _ = p * (p + 1) := mul_comm _ _
    dsimp only [T]
    rw [natTriangular_real_eq, Nat.cast_sub hN]
    norm_num only [Nat.cast_one]
    linarith only [hprod]
  have hTq : ((T : ℕ) : ℤ) + 1 ≤ q := by
    have hlt : ((T : ℕ) : ℤ) < q := by
      exact (Int.lt_ceil).2 (by simpa only [q] using! hTlt)
    omega
  have hB1 : 1 ≤ B := one_le_two.trans hB
  have hpowq : B ^ (T + 1) ≤ B ^ q := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ hB1 (by exact_mod_cast hTq)
  have htwopow : 2 * B ^ T ≤ B ^ q := by
    calc
      2 * B ^ T ≤ B * B ^ T :=
        mul_le_mul_of_nonneg_right hB (by positivity)
      _ = B ^ (T + 1) := by rw [pow_succ]; ring
      _ ≤ B ^ q := hpowq
  have hNB : (N : ℝ) * B ^ T ≤ p * B ^ q := by
    calc
      (N : ℝ) * B ^ T ≤ (2 * p) * B ^ T :=
        mul_le_mul_of_nonneg_right hN2p (by positivity)
      _ = p * (2 * B ^ T) := by ring
      _ ≤ p * B ^ q := mul_le_mul_of_nonneg_left htwopow hp0.le
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hDN0 : 0 ≤ DN := by dsimp only [DN]; positivity
  have hDp1 : 1 ≤ Dp := by
    have hterm : 0 ≤ 2 * p * B ^ q * (1 + Real.log B) := by positivity
    dsimp only [Dp]
    exact le_add_of_nonneg_right hterm
  have hD : DN ≤ Dp := by
    have hfac : 0 ≤ 2 * (1 + Real.log B) := by positivity
    dsimp only [DN, Dp]
    calc
      1 + 2 * (N : ℝ) * (1 + Real.log B) * B ^ T =
          1 + (2 * (1 + Real.log B)) * ((N : ℝ) * B ^ T) := by ring
      _ ≤ 1 + (2 * (1 + Real.log B)) * (p * B ^ q) :=
        by simpa only [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hNB hfac) 1
      _ = 1 + 2 * p * B ^ q * (1 + Real.log B) := by ring
  have hinv : (N : ℝ)⁻¹ ≤ 1 / p := by
    rw [one_div]
    exact (inv_le_inv₀ hNpos hp0).2 hpN
  have hroot : DN ^ ((N : ℝ)⁻¹) ≤ Dp ^ (1 / p) := by
    calc
      DN ^ ((N : ℝ)⁻¹) ≤ Dp ^ ((N : ℝ)⁻¹) :=
        Real.rpow_le_rpow hDN0 hD (inv_nonneg.mpr hNpos.le)
      _ ≤ Dp ^ (1 / p) := Real.rpow_le_rpow_of_exponent_le hDp1 hinv
  have hexp : ENNReal.ofReal p ≤ ENNReal.ofReal (N : ℝ) :=
    ENNReal.ofReal_le_ofReal hpN
  calc
    eLpNorm W (ENNReal.ofReal p) μ ≤ eLpNorm W (ENNReal.ofReal (N : ℝ)) μ :=
      eLpNorm_le_eLpNorm_of_exponent_le hexp hWm.aestronglyMeasurable
    _ ≤ ENNReal.ofReal (DN ^ ((N : ℝ)⁻¹)) := by
      simpa only [DN, T] using eLpNorm_le_integer_of_strongPsiTail
        N hN hB hGrowth hAdmissible hWm hW0 htail
    _ ≤ ENNReal.ofReal (Dp ^ (1 / p)) := ENNReal.ofReal_le_ofReal hroot
    _ = ENNReal.ofReal
        ((1 + 2 * p * B ^ (⌈p * (p + 1) / 2⌉ : ℤ) * (1 + Real.log B)) ^
          (1 / p)) := by rfl

end
end IndependentSums
end Homogenization
