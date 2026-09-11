/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileCarriers

/-!
# The profile bad-event majorant

This file proves the small-profile estimate for the two-branch majorant used on
the bad event of the response estimate.  It is the scalar step that turns
the total-history and drift caps into the response-window constant
`2^(Q/2) eta^(1/2)`.
-/

namespace Homogenization.HighContrast.Response

noncomputable section

/-- If the total history is at most `eta` and the drift is at most `eta / 2`,
the first branch of the correlated bad-event majorant is bounded by
`2^(Q/2) eta^(1/2)`. -/
theorem profileBadMajorant_le_of_small {Q h beta eta : ℝ}
    (hQ : 2 < Q) (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 2)
    (hh0 : 0 ≤ h) (hh : h ≤ eta)
    (hbeta : beta ≤ eta / 2) :
    profileBadMajorant Q h beta ≤
      (2 : ℝ) ^ (Q / 2) * eta ^ (1 / 2 : ℝ) := by
  have hQ0 : 0 < Q := lt_trans (by norm_num) hQ
  have hinv0 : 0 < Q⁻¹ := inv_pos.mpr hQ0
  have hinvHalf : Q⁻¹ < (2 : ℝ)⁻¹ :=
    (inv_lt_inv₀ hQ0 (by norm_num)).2 hQ
  have hinvHalf' : Q⁻¹ < 1 / 2 := by
    simpa only [one_div] using hinvHalf
  have hexp0 : 0 < 1 / 2 - Q⁻¹ := by
    linarith only [hinvHalf']
  have hetaLe1 : eta ≤ 1 := by linarith only [heta1]
  have hbetaHalf : beta ≤ 1 / 2 := by
    calc beta ≤ eta / 2 := hbeta
      _ ≤ 1 / 2 := by linarith only [heta1]
  have hbetaLt : beta < 1 := lt_of_le_of_lt hbetaHalf (by norm_num)
  have hpowInv : h ^ Q⁻¹ ≤ eta ^ Q⁻¹ :=
    Real.rpow_le_rpow hh0 hh hinv0.le
  have hpowRest : h ^ (1 / 2 - Q⁻¹) ≤
      eta ^ (1 / 2 - Q⁻¹) :=
    Real.rpow_le_rpow hh0 hh hexp0.le
  have hinvLeOne : Q⁻¹ ≤ 1 := by linarith only [hinvHalf']
  have hetaLePow : eta ≤ eta ^ Q⁻¹ := by
    calc
      eta = eta ^ (1 : ℝ) := (Real.rpow_one eta).symm
      _ ≤ eta ^ Q⁻¹ :=
        Real.rpow_le_rpow_of_exponent_ge heta0 hetaLe1 hinvLeOne
  have hbetaPow : beta ≤ eta ^ Q⁻¹ := by
    exact hbeta.trans (by linarith only [heta0, hetaLePow])
  have hsum : h ^ Q⁻¹ + beta ≤ 2 * eta ^ Q⁻¹ := by
    linarith only [hpowInv, hbetaPow]
  have hcore :
      (h ^ Q⁻¹ + beta) * h ^ (1 / 2 - Q⁻¹) ≤
        2 * eta ^ (1 / 2 : ℝ) := by
    have hmul := mul_le_mul hsum hpowRest
      (Real.rpow_nonneg hh0 _) (by positivity : 0 ≤ 2 * eta ^ Q⁻¹)
    calc
      (h ^ Q⁻¹ + beta) * h ^ (1 / 2 - Q⁻¹)
          ≤ (2 * eta ^ Q⁻¹) * eta ^ (1 / 2 - Q⁻¹) := hmul
      _ = 2 * eta ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add heta0]
        congr 1
        ring_nf
  have hbase : (1 / 2 : ℝ) ≤ 1 - beta := by
    linarith only [hbetaHalf]
  have hneg : 1 - Q / 2 ≤ 0 := by linarith only [hQ]
  have hfactorRaw :
      (1 - beta) ^ (1 - Q / 2) ≤ (1 / 2 : ℝ) ^ (1 - Q / 2) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hbase hneg
  have hhalfPow :
      (1 / 2 : ℝ) ^ (1 - Q / 2) = (2 : ℝ) ^ (Q / 2 - 1) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring_nf
  have hfactor :
      (1 - beta) ^ (1 - Q / 2) ≤ (2 : ℝ) ^ (Q / 2 - 1) := by
    rw [← hhalfPow]
    exact hfactorRaw
  have htwoPow :
      2 * (2 : ℝ) ^ (Q / 2 - 1) = (2 : ℝ) ^ (Q / 2) := by
    calc
      2 * (2 : ℝ) ^ (Q / 2 - 1) =
          (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (Q / 2 - 1) := by
            rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((1 : ℝ) + (Q / 2 - 1)) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = (2 : ℝ) ^ (Q / 2) := by
        congr 1
        ring_nf
  rw [profileBadMajorant_of_lt_one hbetaLt]
  have hfinal := mul_le_mul hcore hfactor
    (Real.rpow_nonneg (by linarith only [hbetaLt]) _)
    (by positivity : 0 ≤ 2 * eta ^ (1 / 2 : ℝ))
  calc
    (h ^ Q⁻¹ + beta) * (1 - beta) ^ (1 - Q / 2) *
          h ^ (1 / 2 - Q⁻¹)
        = ((h ^ Q⁻¹ + beta) * h ^ (1 / 2 - Q⁻¹)) *
            (1 - beta) ^ (1 - Q / 2) := by ring
    _ ≤ (2 * eta ^ (1 / 2 : ℝ)) * (2 : ℝ) ^ (Q / 2 - 1) := hfinal
    _ = (2 * (2 : ℝ) ^ (Q / 2 - 1)) * eta ^ (1 / 2 : ℝ) := by ring
    _ = (2 : ℝ) ^ (Q / 2) * eta ^ (1 / 2 : ℝ) := by rw [htwoPow]

end

end Homogenization.HighContrast.Response
