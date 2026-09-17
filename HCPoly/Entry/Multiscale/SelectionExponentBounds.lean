import HCPoly.Entry.Setup.SelectionExponents
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds for the fixed selection exponents

This file proves the elementary arithmetic consequences of the definitions
`bigQ` and `rhoMax` used in the scale-selection and two-grid estimates.
-/

namespace Homogenization.HighContrast.Multiscale

open Homogenization.HighContrast

noncomputable section

theorem bigQ_even (d : ℕ) (γ : ℝ) : Even (bigQ d γ) := by
  refine ⟨⌈2 * ((d : ℝ) + 1) / (1 - γ)⌉₊, ?_⟩
  simpa [bigQ] using (two_mul ⌈2 * ((d : ℝ) + 1) / (1 - γ)⌉₊)

private theorem bigQ_two_le_of_lt_one (d : ℕ) {γ : ℝ} (hγlt : γ < 1) :
    2 ≤ bigQ d γ := by
  have hden : 0 < 1 - γ := sub_pos.mpr hγlt
  have harg_pos : 0 < 2 * ((d : ℝ) + 1) / (1 - γ) := by
    positivity
  have hceil : 1 ≤ ⌈2 * ((d : ℝ) + 1) / (1 - γ)⌉₊ :=
    (Nat.one_le_ceil_iff).2 harg_pos
  unfold bigQ
  nlinarith

theorem bigQ_two_le (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : 2 ≤ bigQ d γ := by
  exact bigQ_two_le_of_lt_one d hγ.2

theorem bigQ_pos (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : 0 < bigQ d γ := by
  exact lt_of_lt_of_le (by norm_num : 0 < 2) (bigQ_two_le d hd γ hγ)

theorem bigQ_ne_zero (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : bigQ d γ ≠ 0 :=
  (bigQ_pos d hd γ hγ).ne'

theorem bigQ_real_pos (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : 0 < (bigQ d γ : ℝ) := by
  exact_mod_cast bigQ_pos d hd γ hγ

theorem bigQ_mul_one_sub_ge (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    4 * ((d : ℝ) + 1) ≤ (bigQ d γ : ℝ) * (1 - γ) := by
  have hden : 0 < 1 - γ := sub_pos.mpr hγ.2
  let x : ℝ := 2 * ((d : ℝ) + 1) / (1 - γ)
  have hx_le : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hmul := mul_le_mul_of_nonneg_right hx_le (show 0 ≤ 2 * (1 - γ) by positivity)
  have hleft : x * (2 * (1 - γ)) = 4 * ((d : ℝ) + 1) := by
    dsimp [x]
    field_simp [hden.ne']
    ring_nf
  have hright :
      (⌈x⌉₊ : ℝ) * (2 * (1 - γ)) = (bigQ d γ : ℝ) * (1 - γ) := by
    simp [x, bigQ, mul_assoc, mul_comm]
  calc
    4 * ((d : ℝ) + 1) = x * (2 * (1 - γ)) := hleft.symm
    _ ≤ (⌈x⌉₊ : ℝ) * (2 * (1 - γ)) := hmul
    _ = (bigQ d γ : ℝ) * (1 - γ) := hright

private theorem rhoMax_numerator_lt_bigQ_mul_one_sub (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    (d : ℝ) + (1 - γ) / 4 < (bigQ d γ : ℝ) * (1 - γ) := by
  have hbound := bigQ_mul_one_sub_ge d hd γ hγ
  have hγ_nonneg : 0 ≤ γ := hγ.1
  have hγlt : γ < 1 := hγ.2
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  have hnum_lt : (d : ℝ) + (1 - γ) / 4 < 4 * ((d : ℝ) + 1) := by
    nlinarith
  exact hnum_lt.trans_le hbound

theorem rhoMax_lt_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : rhoMax d γ < 1 := by
  have hq_pos : 0 < (bigQ d γ : ℝ) := bigQ_real_pos d hd γ hγ
  have hnum_lt := rhoMax_numerator_lt_bigQ_mul_one_sub d hd γ hγ
  have hfrac_lt : (bigQ d γ : ℝ)⁻¹ * ((d : ℝ) + (1 - γ) / 4) < 1 - γ := by
    rw [inv_mul_eq_div]
    exact (div_lt_iff₀ hq_pos).2 (by simpa [mul_comm] using hnum_lt)
  simp [rhoMax]
  linarith

theorem gamma_le_rhoMax (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : γ ≤ rhoMax d γ := by
  have hq_nonneg : 0 ≤ ((bigQ d γ : ℝ)⁻¹) := by
    exact inv_nonneg.mpr (le_of_lt (bigQ_real_pos d hd γ hγ))
  have hnum_nonneg : 0 ≤ (d : ℝ) + (1 - γ) / 4 := by
    have hgap : 0 ≤ 1 - γ := sub_nonneg.mpr hγ.2.le
    positivity
  simp [rhoMax]
  exact mul_nonneg hq_nonneg hnum_nonneg

theorem rhoMax_sub_d_div_bigQ (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    rhoMax d γ - (d : ℝ) / (bigQ d γ : ℝ) =
      γ + (1 - γ) / (4 * (bigQ d γ : ℝ)) := by
  have hq_ne : (bigQ d γ : ℝ) ≠ 0 := ne_of_gt (bigQ_real_pos d hd γ hγ)
  simp [rhoMax, inv_mul_eq_div]
  field_simp [hq_ne]
  ring

theorem fluctuation_decay_exponent_pos (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    0 < (d : ℝ) / 2 - (1 - γ) / (4 * (bigQ d γ : ℝ)) := by
  have hq_two : (2 : ℝ) ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast bigQ_two_le d hd γ hγ
  have hq_pos : 0 < (bigQ d γ : ℝ) := lt_of_lt_of_le zero_lt_two hq_two
  have hd_two : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hgap_le_one : 1 - γ ≤ 1 := by linarith [hγ.1]
  have hgap_nonneg : 0 ≤ 1 - γ := sub_nonneg.mpr hγ.2.le
  have hden_pos : 0 < 4 * (bigQ d γ : ℝ) := by positivity
  have hsmall : (1 - γ) / (4 * (bigQ d γ : ℝ)) ≤ 1 / 8 := by
    have hden_ge : (8 : ℝ) ≤ 4 * (bigQ d γ : ℝ) := by nlinarith
    calc
      (1 - γ) / (4 * (bigQ d γ : ℝ)) ≤ 1 / (4 * (bigQ d γ : ℝ)) := by
        exact div_le_div_of_nonneg_right hgap_le_one hden_pos.le
      _ ≤ 1 / 8 := by
        exact one_div_le_one_div_of_le (by norm_num) hden_ge
  nlinarith

/-- The moment order used in the source multiplier tail estimate. -/
def sourceMomentExponent (d : ℕ) (γ : ℝ) : ℕ :=
  2 * (d + bigQ d γ)

theorem sourceMomentExponent_ge_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    1 ≤ sourceMomentExponent d γ := by
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd
  unfold sourceMomentExponent
  nlinarith [Nat.le_add_right d (bigQ d γ)]

/-- Explicit margins for the two geometric tails in the argument for `e.source.multiplier`. -/
theorem sourceMomentExponent_tail_margins (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    (d : ℝ) + (bigQ d γ : ℝ) ≤ (sourceMomentExponent d γ : ℝ) - (d : ℝ) ∧
    (d : ℝ) + (bigQ d γ : ℝ) ≤
      (sourceMomentExponent d γ : ℝ) - (bigQ d γ : ℝ) * γ := by
  have hQ : 0 ≤ (bigQ d γ : ℝ) := (bigQ_real_pos d hd γ hγ).le
  have hγ1 : 0 ≤ 1 - γ := sub_nonneg.mpr hγ.2.le
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  simp only [sourceMomentExponent, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]
  constructor <;> nlinarith [mul_nonneg hQ hγ1]

end

end Homogenization.HighContrast.Multiscale
