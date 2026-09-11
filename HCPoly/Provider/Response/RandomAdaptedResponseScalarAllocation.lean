/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseInsertion

/-!
# Scalar allocation for the compact response bound

The calibrated pairwise products in the compact mixed bound are collected
without converting an extended-nonnegative row or weak quantity to a real.
-/

namespace Homogenization.HighContrast.Response

open scoped ENNReal

noncomputable section

private theorem sqrt_half_le_self {k : ℝ} (hk : 1 ≤ k) : Real.sqrt k ≤ k := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  refine (Real.sqrt_le_iff).2 ⟨hk0, ?_⟩
  calc
    k = k * 1 := (mul_one k).symm
    _ ≤ k * k := mul_le_mul_of_nonneg_left hk hk0
    _ = k ^ 2 := by ring

private theorem sqrt_mul_sqrt_half (T k : ℝ) (hT : 0 ≤ T) :
    Real.sqrt (T * Real.sqrt k) = Real.sqrt T * Real.sqrt (Real.sqrt k) := by
  rw [Real.sqrt_mul hT]

private theorem sqrt_row_scale (L k : ℝ) (hL : 0 ≤ L) (hk : 1 ≤ k) :
    Real.sqrt (L * k ^ (3 / 2 : ℝ)) =
      Real.sqrt L * Real.sqrt k * Real.sqrt (Real.sqrt k) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  rw [Real.sqrt_mul hL, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow]
  rw [Real.sqrt_eq_rpow (k ^ (1 / 2 : ℝ))]
  rw [← Real.rpow_mul hk0.le (3 / 2) (1 / 2),
    ← Real.rpow_mul hk0.le (1 / 2) (1 / 2)]
  rw [show L ^ (1 / 2 : ℝ) * k ^ (1 / 2 : ℝ) *
      k ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) =
      L ^ (1 / 2 : ℝ) *
        (k ^ (1 / 2 : ℝ) * k ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ))) by ring]
  rw [← Real.rpow_add hk0]
  congr 2
  all_goals norm_num

private theorem sqrt_tau_row_scale (T L k : ℝ)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hk : 1 ≤ k) :
    Real.sqrt (T * Real.sqrt k) * Real.sqrt (L * k ^ (3 / 2 : ℝ)) =
      Real.sqrt (T * L) * k := by
  rw [sqrt_mul_sqrt_half T k hT, sqrt_row_scale L k hL hk,
    Real.sqrt_mul hT]
  have hs : Real.sqrt (Real.sqrt k) * Real.sqrt (Real.sqrt k) =
      Real.sqrt k := by
    rw [Real.mul_self_sqrt (Real.sqrt_nonneg k)]
  have hsk : Real.sqrt k * Real.sqrt k = k :=
    Real.mul_self_sqrt (le_trans zero_le_one hk)
  calc
    Real.sqrt T * Real.sqrt (Real.sqrt k) *
          (Real.sqrt L * Real.sqrt k * Real.sqrt (Real.sqrt k)) =
        Real.sqrt T * Real.sqrt L *
          (Real.sqrt k *
            (Real.sqrt (Real.sqrt k) * Real.sqrt (Real.sqrt k))) := by ring
    _ = Real.sqrt T * Real.sqrt L * (Real.sqrt k * Real.sqrt k) := by rw [hs]
    _ = Real.sqrt T * Real.sqrt L * k := by rw [hsk]

private theorem sqrt_tau_energy_scale (T A k : ℝ)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hk : 1 ≤ k) :
    Real.sqrt (T * Real.sqrt k) * Real.sqrt (A * Real.sqrt k) ≤
      Real.sqrt (T * A) * k := by
  rw [sqrt_mul_sqrt_half T k hT,
    sqrt_mul_sqrt_half A k hA, Real.sqrt_mul hT]
  have hs : Real.sqrt (Real.sqrt k) * Real.sqrt (Real.sqrt k) =
      Real.sqrt k := by
    rw [Real.mul_self_sqrt (Real.sqrt_nonneg k)]
  calc
    Real.sqrt T * Real.sqrt (Real.sqrt k) *
          (Real.sqrt A * Real.sqrt (Real.sqrt k)) =
        Real.sqrt T * Real.sqrt A *
          (Real.sqrt (Real.sqrt k) * Real.sqrt (Real.sqrt k)) := by ring
    _ = Real.sqrt T * Real.sqrt A * Real.sqrt k := by rw [hs]
    _ ≤ Real.sqrt T * Real.sqrt A * k :=
      mul_le_mul_of_nonneg_left (sqrt_half_le_self hk)
        (mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg A))

/-- Literal defect, energy, and extended-nonnegative row bounds yield the five
mixed products consumed by the compact scalar allocation. -/
theorem calibrated_mixed_products
    {tau EJ T A L kappa : ℝ} {row : ℝ≥0∞}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hkappa : 1 ≤ kappa)
    (htau : tau ≤ T * Real.sqrt kappa)
    (hEJ : EJ ≤ A * Real.sqrt kappa)
    (hrow : row ≤ ENNReal.ofReal (L * kappa ^ (3 / 2 : ℝ))) :
    let a := ENNReal.ofReal (Real.sqrt tau)
    let b := ENNReal.ofReal (Real.sqrt EJ)
    let r := row ^ (1 / 2 : ℝ)
    a * a ≤ ENNReal.ofReal (T * kappa) ∧
      a * b ≤ ENNReal.ofReal (Real.sqrt (T * A) * kappa) ∧
      a * r ≤ ENNReal.ofReal (Real.sqrt (T * L) * kappa) ∧
      b * b ≤ ENNReal.ofReal (A * kappa) ∧
      b * r ≤ ENNReal.ofReal (Real.sqrt (A * L) * kappa) := by
  dsimp only
  have hkappa0 : 0 ≤ kappa := le_trans zero_le_one hkappa
  have hTk0 : 0 ≤ T * Real.sqrt kappa :=
    mul_nonneg hT (Real.sqrt_nonneg kappa)
  have hAk0 : 0 ≤ A * Real.sqrt kappa :=
    mul_nonneg hA (Real.sqrt_nonneg kappa)
  have hLk0 : 0 ≤ L * kappa ^ (3 / 2 : ℝ) :=
    mul_nonneg hL (Real.rpow_nonneg hkappa0 _)
  have ha : ENNReal.ofReal (Real.sqrt tau) ≤
      ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa)) :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt htau)
  have hb : ENNReal.ofReal (Real.sqrt EJ) ≤
      ENNReal.ofReal (Real.sqrt (A * Real.sqrt kappa)) :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hEJ)
  have hr : row ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (L * kappa ^ (3 / 2 : ℝ))) := by
    calc
      row ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (L * kappa ^ (3 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hrow (by norm_num)
      _ = ENNReal.ofReal ((L * kappa ^ (3 / 2 : ℝ)) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg hLk0 (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (L * kappa ^ (3 / 2 : ℝ))) := by
        rw [Real.sqrt_eq_rpow]
  have haa : ENNReal.ofReal (Real.sqrt tau) * ENNReal.ofReal (Real.sqrt tau) ≤
      ENNReal.ofReal (T * kappa) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa)) *
          ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa)) := mul_le_mul' ha ha
      _ = ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa) *
          Real.sqrt (T * Real.sqrt kappa)) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (T * Real.sqrt kappa) := by rw [Real.mul_self_sqrt hTk0]
      _ ≤ ENNReal.ofReal (T * kappa) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (sqrt_half_le_self hkappa) hT)
  have hab : ENNReal.ofReal (Real.sqrt tau) * ENNReal.ofReal (Real.sqrt EJ) ≤
      ENNReal.ofReal (Real.sqrt (T * A) * kappa) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa)) *
          ENNReal.ofReal (Real.sqrt (A * Real.sqrt kappa)) := mul_le_mul' ha hb
      _ = ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa) *
          Real.sqrt (A * Real.sqrt kappa)) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ ≤ ENNReal.ofReal (Real.sqrt (T * A) * kappa) :=
        ENNReal.ofReal_le_ofReal (sqrt_tau_energy_scale T A kappa hT hA hkappa)
  have har : ENNReal.ofReal (Real.sqrt tau) * row ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (T * L) * kappa) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa)) *
          ENNReal.ofReal (Real.sqrt (L * kappa ^ (3 / 2 : ℝ))) :=
        mul_le_mul' ha hr
      _ = ENNReal.ofReal (Real.sqrt (T * Real.sqrt kappa) *
          Real.sqrt (L * kappa ^ (3 / 2 : ℝ))) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (Real.sqrt (T * L) * kappa) := by
        rw [sqrt_tau_row_scale T L kappa hT hL hkappa]
  have hbb : ENNReal.ofReal (Real.sqrt EJ) * ENNReal.ofReal (Real.sqrt EJ) ≤
      ENNReal.ofReal (A * kappa) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt (A * Real.sqrt kappa)) *
          ENNReal.ofReal (Real.sqrt (A * Real.sqrt kappa)) := mul_le_mul' hb hb
      _ = ENNReal.ofReal (Real.sqrt (A * Real.sqrt kappa) *
          Real.sqrt (A * Real.sqrt kappa)) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (A * Real.sqrt kappa) := by rw [Real.mul_self_sqrt hAk0]
      _ ≤ ENNReal.ofReal (A * kappa) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (sqrt_half_le_self hkappa) hA)
  have hbr : ENNReal.ofReal (Real.sqrt EJ) * row ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (A * L) * kappa) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt (A * Real.sqrt kappa)) *
          ENNReal.ofReal (Real.sqrt (L * kappa ^ (3 / 2 : ℝ))) :=
        mul_le_mul' hb hr
      _ = ENNReal.ofReal (Real.sqrt (A * Real.sqrt kappa) *
          Real.sqrt (L * kappa ^ (3 / 2 : ℝ))) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ = ENNReal.ofReal (Real.sqrt (A * L) * kappa) := by
        rw [sqrt_tau_row_scale A L kappa hA hL hkappa]
  exact ⟨haa, hab, har, hbb, hbr⟩

/-- The five calibrated products and the weak allocation give one half of
the response coefficient. -/
theorem compact_pre_young_allocation
    {C expo T A L R kappa : ℝ} {a b r w : ℝ≥0∞}
    (hC : 0 ≤ C) (hexpo : 0 ≤ expo) (hT : 0 ≤ T)
    (hTA : 0 ≤ Real.sqrt (T * A))
    (hTL : 0 ≤ Real.sqrt (T * L)) (hA : 0 ≤ A)
    (hAL : 0 ≤ Real.sqrt (A * L)) (hR : 0 ≤ R ^ 2)
    (hkappa : 0 ≤ kappa)
    (haa : a * a ≤ ENNReal.ofReal (T * kappa))
    (hab : a * b ≤ ENNReal.ofReal (Real.sqrt (T * A) * kappa))
    (har : a * r ≤ ENNReal.ofReal (Real.sqrt (T * L) * kappa))
    (hbb : b * b ≤ ENNReal.ofReal (A * kappa))
    (hbr : b * r ≤ ENNReal.ofReal (Real.sqrt (A * L) * kappa))
    (hw : w ≤ ENNReal.ofReal (R ^ 2 * kappa)) :
    ENNReal.ofReal C * a * (a + b + r) +
          ENNReal.ofReal C * ENNReal.ofReal expo * b * (b + r) +
          ENNReal.ofReal C * w ≤
      ENNReal.ofReal
        (C * (T + Real.sqrt (T * A) + Real.sqrt (T * L) +
          expo * (A + Real.sqrt (A * L)) + R ^ 2) * kappa) := by
  have hCa : ENNReal.ofReal C * (a * a) ≤
      ENNReal.ofReal (C * (T * kappa)) := by
    calc
      ENNReal.ofReal C * (a * a) ≤
          ENNReal.ofReal C * ENNReal.ofReal (T * kappa) :=
        by gcongr
      _ = ENNReal.ofReal (C * (T * kappa)) := by
        rw [ENNReal.ofReal_mul hC]
  have hCab : ENNReal.ofReal C * (a * b) ≤
      ENNReal.ofReal (C * (Real.sqrt (T * A) * kappa)) := by
    calc
      ENNReal.ofReal C * (a * b) ≤
          ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (T * A) * kappa) :=
        by gcongr
      _ = ENNReal.ofReal (C * (Real.sqrt (T * A) * kappa)) := by
        rw [ENNReal.ofReal_mul hC]
  have hCar : ENNReal.ofReal C * (a * r) ≤
      ENNReal.ofReal (C * (Real.sqrt (T * L) * kappa)) := by
    calc
      ENNReal.ofReal C * (a * r) ≤
          ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (T * L) * kappa) :=
        by gcongr
      _ = ENNReal.ofReal (C * (Real.sqrt (T * L) * kappa)) := by
        rw [ENNReal.ofReal_mul hC]
  have hCebb : ENNReal.ofReal C * ENNReal.ofReal expo * (b * b) ≤
      ENNReal.ofReal (C * (expo * (A * kappa))) := by
    calc
      ENNReal.ofReal C * ENNReal.ofReal expo * (b * b) ≤
          ENNReal.ofReal C * ENNReal.ofReal expo *
            ENNReal.ofReal (A * kappa) := by gcongr
      _ = ENNReal.ofReal (C * (expo * (A * kappa))) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hexpo]
        ring
  have hCebr : ENNReal.ofReal C * ENNReal.ofReal expo * (b * r) ≤
      ENNReal.ofReal (C * (expo * (Real.sqrt (A * L) * kappa))) := by
    calc
      ENNReal.ofReal C * ENNReal.ofReal expo * (b * r) ≤
          ENNReal.ofReal C * ENNReal.ofReal expo *
            ENNReal.ofReal (Real.sqrt (A * L) * kappa) :=
        by gcongr
      _ = ENNReal.ofReal
          (C * (expo * (Real.sqrt (A * L) * kappa))) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hexpo]
        ring
  have hCw : ENNReal.ofReal C * w ≤
      ENNReal.ofReal (C * (R ^ 2 * kappa)) := by
    calc
      ENNReal.ofReal C * w ≤
          ENNReal.ofReal C * ENNReal.ofReal (R ^ 2 * kappa) :=
        by gcongr
      _ = ENNReal.ofReal (C * (R ^ 2 * kappa)) := by
        rw [ENNReal.ofReal_mul hC]
  conv_lhs => rw [mul_add, mul_add, mul_add]
  calc
    ENNReal.ofReal C * a * a + ENNReal.ofReal C * a * b +
          ENNReal.ofReal C * a * r +
          (ENNReal.ofReal C * ENNReal.ofReal expo * b * b +
            ENNReal.ofReal C * ENNReal.ofReal expo * b * r) +
          ENNReal.ofReal C * w ≤
        ENNReal.ofReal (C * (T * kappa)) +
          ENNReal.ofReal (C * (Real.sqrt (T * A) * kappa)) +
          ENNReal.ofReal (C * (Real.sqrt (T * L) * kappa)) +
          (ENNReal.ofReal (C * (expo * (A * kappa))) +
            ENNReal.ofReal
              (C * (expo * (Real.sqrt (A * L) * kappa)))) +
          ENNReal.ofReal (C * (R ^ 2 * kappa)) := by
      simpa only [mul_assoc, add_assoc] using
        add_le_add (add_le_add (add_le_add hCa hCab) hCar)
          (add_le_add (add_le_add hCebb hCebr) hCw)
    _ = ENNReal.ofReal
        (C * (T + Real.sqrt (T * A) + Real.sqrt (T * L) +
          expo * (A + Real.sqrt (A * L)) + R ^ 2) * kappa) := by
      let x1 := C * (T * kappa)
      let x2 := C * (Real.sqrt (T * A) * kappa)
      let x3 := C * (Real.sqrt (T * L) * kappa)
      let x4 := C * (expo * (A * kappa))
      let x5 := C * (expo * (Real.sqrt (A * L) * kappa))
      let x6 := C * (R ^ 2 * kappa)
      have hx1 : 0 ≤ x1 := mul_nonneg hC (mul_nonneg hT hkappa)
      have hx2 : 0 ≤ x2 := mul_nonneg hC (mul_nonneg hTA hkappa)
      have hx3 : 0 ≤ x3 := mul_nonneg hC (mul_nonneg hTL hkappa)
      have hx4 : 0 ≤ x4 :=
        mul_nonneg hC (mul_nonneg hexpo (mul_nonneg hA hkappa))
      have hx5 : 0 ≤ x5 :=
        mul_nonneg hC (mul_nonneg hexpo (mul_nonneg hAL hkappa))
      have hx6 : 0 ≤ x6 := mul_nonneg hC (mul_nonneg hR hkappa)
      have hreal :
          x1 + x2 + x3 + (x4 + x5) + x6 =
            C * (T + Real.sqrt (T * A) + Real.sqrt (T * L) +
              expo * (A + Real.sqrt (A * L)) + R ^ 2) * kappa := by
        dsimp only [x1, x2, x3, x4, x5, x6]
        ring
      change ENNReal.ofReal x1 + ENNReal.ofReal x2 + ENNReal.ofReal x3 +
          (ENNReal.ofReal x4 + ENNReal.ofReal x5) + ENNReal.ofReal x6 = _
      rw [← hreal, ENNReal.ofReal_add
          (add_nonneg (add_nonneg (add_nonneg hx1 hx2) hx3)
            (add_nonneg hx4 hx5)) hx6,
        ENNReal.ofReal_add
          (add_nonneg (add_nonneg hx1 hx2) hx3) (add_nonneg hx4 hx5),
        ENNReal.ofReal_add (add_nonneg hx1 hx2) hx3,
        ENNReal.ofReal_add hx1 hx2, ENNReal.ofReal_add hx4 hx5]

end

end Homogenization.HighContrast.Response
