/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The cutoff coefficient of the short test

The last of the five thresholds of `p.successful.short.bridge` is the
cutoff coefficient `B`, chosen after the source allowance and still before the
law.  Its job is to convert the entry-scale clause `r_0 - j_* ≥ B log_3(2 + Π)`
into the source bound `R_i ≤ τ_src`, uniformly in the reference aspect ratio.

Two steps do that.  First, the amortized bound of the hop-index bootstrap
collapses: the exponential factor is at most one because the strict hop-length
requirement among the constants fixed for the bridge test makes its exponent
nonpositive, and the geometric factor is at most `(2 + Π)^{-ρ_dr B/2}` because
the entry-scale
clause bounds its exponent.  What survives is `C(2 + Π)^{1 - ρ_dr B/2}`.

Second, that expression is uniformly small for large `B`: the exponent is
negative, the base is at least three, and so the whole expression is at most
`C3^{1 - ρ_dr B/2}`, which tends to zero.  Choosing `B` so that
`ρ_dr B/2 > 1` and this last quantity is below the source allowance is the
printed choice, and it is uniform for `Π ≥ 1` exactly as stated.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open Real

noncomputable section

/-! ## The amortized bound collapses -/

/-- **The amortized source bound.**  Under the strict hop-length requirement and
the entry-scale clause, the bootstrap's amortized bound is at most
`C(2 + Π)^{1 - ρ_dr B/2}`. -/
theorem amortized_le_rpow {rhoDr B C Pi chop l0 : ℝ} {r0 jStar : ℤ} {k : ℕ} {R : ℝ}
    (hrho : 0 < rhoDr) (hPi : 1 ≤ Pi) (hC : 0 ≤ C)
    (hentry : B * Real.logb 3 (2 + Pi) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hstrict : 2 * chop < rhoDr * l0 * Real.log 3 / 2)
    (hboot : R ≤ C * (2 + Pi) * (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
      Real.exp (-(k : ℝ) * (rhoDr * l0 * Real.log 3 / 2 - 2 * chop))) :
    R ≤ C * (2 + Pi) ^ (1 - rhoDr * B / 2) := by
  have hPi0 : (0 : ℝ) < 2 + Pi := by linarith only [hPi]
  have hbase : (0 : ℝ) ≤ C * (2 + Pi) := mul_nonneg hC hPi0.le
  -- the exponential factor is at most one
  have hexp : Real.exp (-(k : ℝ) * (rhoDr * l0 * Real.log 3 / 2 - 2 * chop)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith only [hk, hstrict]
  -- the geometric factor is at most the printed power of the aspect ratio
  have hgeo : (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) ≤
      (2 + Pi) ^ (-(rhoDr * B / 2)) := by
    have hstep : (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) ≤
        (3 : ℝ) ^ (Real.logb 3 (2 + Pi) * (-(rhoDr * B / 2))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith only [hrho, hentry]
    refine hstep.trans_eq ?_
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) hPi0]
  -- assemble
  have hchain : C * (2 + Pi) * (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
      Real.exp (-(k : ℝ) * (rhoDr * l0 * Real.log 3 / 2 - 2 * chop)) ≤
      C * (2 + Pi) * (2 + Pi) ^ (-(rhoDr * B / 2)) := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) := by positivity
    have hstep₁ := mul_le_mul_of_nonneg_left hexp (mul_nonneg hbase h3)
    have hstep₂ := mul_le_mul_of_nonneg_left hgeo hbase
    rw [mul_one] at hstep₁
    exact hstep₁.trans hstep₂
  have hsplit : (2 + Pi) ^ (1 - rhoDr * B / 2) =
      (2 + Pi) * (2 + Pi) ^ (-(rhoDr * B / 2)) := by
    rw [show (1 : ℝ) - rhoDr * B / 2 = 1 + -(rhoDr * B / 2) by ring, Real.rpow_add hPi0,
      Real.rpow_one]
  refine (hboot.trans hchain).trans_eq ?_
  rw [hsplit]
  ring

/-! ## The choice of the cutoff coefficient -/

/-- **The choice of `B`.**  A cutoff coefficient exists that meets the fourth
requirement among the constants fixed for the bridge test and puts the amortized
source bound below the source allowance, uniformly for reference aspect ratios at
least one. -/
theorem exists_cutoff {rhoDr C tauSrc : ℝ} (hrho : 0 < rhoDr) (hC : 0 < C)
    (htau : 0 < tauSrc) :
    ∃ B : ℝ, 0 < B ∧ 1 < rhoDr * B / 2 ∧
      ∀ Pi : ℝ, 1 ≤ Pi → C * (2 + Pi) ^ (1 - rhoDr * B / 2) ≤ tauSrc := by
  set s : ℝ := 1 + max 1 (Real.logb 3 (C / tauSrc)) with hs
  have hs2 : 2 ≤ s := by
    have : (1 : ℝ) ≤ max 1 (Real.logb 3 (C / tauSrc)) := le_max_left _ _
    linarith only [this]
  refine ⟨2 * s / rhoDr, by positivity, ?_, fun Pi hPi => ?_⟩
  · rw [show rhoDr * (2 * s / rhoDr) / 2 = s by field_simp]
    linarith only [hs2]
  · rw [show rhoDr * (2 * s / rhoDr) / 2 = s by field_simp]
    have hPi0 : (0 : ℝ) < 2 + Pi := by linarith only [hPi]
    have h3le : (3 : ℝ) ≤ 2 + Pi := by linarith only [hPi]
    -- the base is at least three and the exponent is negative
    have hpow : (3 : ℝ) ^ (s - 1) ≤ (2 + Pi) ^ (s - 1) :=
      Real.rpow_le_rpow (by norm_num) h3le (by linarith only [hs2])
    have hpos3 : (0 : ℝ) < (3 : ℝ) ^ (s - 1) := by positivity
    have hinv : (2 + Pi) ^ (1 - s) ≤ ((3 : ℝ) ^ (s - 1))⁻¹ := by
      rw [show (1 : ℝ) - s = -(s - 1) by ring, Real.rpow_neg hPi0.le]
      exact inv_anti₀ hpos3 hpow
    -- the geometric factor absorbs the ratio of the constant to the allowance
    have hratio : C / tauSrc ≤ (3 : ℝ) ^ (s - 1) := by
      have hle : Real.logb 3 (C / tauSrc) ≤ s - 1 := by
        have : Real.logb 3 (C / tauSrc) ≤ max 1 (Real.logb 3 (C / tauSrc)) := le_max_right _ _
        rw [hs]; linarith only [this]
      have hmono : (3 : ℝ) ^ Real.logb 3 (C / tauSrc) ≤ (3 : ℝ) ^ (s - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (div_pos hC htau)] at hmono
    have hfinal := mul_le_mul_of_nonneg_left hinv hC.le
    refine hfinal.trans ?_
    rw [mul_inv_le_iff₀ hpos3]
    rw [div_le_iff₀ htau] at hratio
    linarith only [hratio]

end

end ShortHop
end HighContrast
end Homogenization
