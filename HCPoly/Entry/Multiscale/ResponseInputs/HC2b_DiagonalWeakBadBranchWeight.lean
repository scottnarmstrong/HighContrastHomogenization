import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentDegenerate

/-!
# The bad-branch weight arithmetic of the cell-average estimate

On the event `{M > 1}` of the all-scale maximum `M`, the cell-average estimate is absorbed by
its tail term, and the only remaining input is the geometric comparison of the weights
`3^{-a j}`.  This file records that comparison as plain real arithmetic: a geometric series with
ratio `3^{-a}`, the reciprocal bound `(1 - 3^{-a})^{-1} ≤ 3/a` on `0 < a ≤ 1`, its value
`(1 - 3^{-1/2})^{-1} ≤ 3` at `a = 1/2`, and the assembled bad-branch weight bound in terms of the
response parameters `respAlpha` and `respRho`.
-/

namespace Homogenization.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The tail weights `3^{-(a j)}` sum to the geometric series with ratio `3^{-a}`. -/
theorem h6a_geom_sum_rpow (a : ℝ) (ha : 0 < a) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) = (1 - (3 : ℝ) ^ (-a))⁻¹ := by
  have hterm : ∀ j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) = ((3 : ℝ) ^ (-a)) ^ j := by
    intro j
    rw [show -(a * (j : ℝ)) = (-a) * (j : ℝ) by ring]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  rw [tsum_congr hterm]
  exact tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

/-- On `0 < a ≤ 1` the reciprocal of `1 - 3^{-a}` is at most `3 / a`. -/
theorem h6a_inv_one_sub_rpow_le (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (1 - (3 : ℝ) ^ (-a))⁻¹ ≤ 3 / a := by
  have hexp1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr hexp1
  have hlog0 : 0 < Real.log 3 := lt_trans zero_lt_one hlog
  set x : ℝ := a * Real.log 3 with hxdef
  have hx_pos : 0 < x := by
    rw [hxdef]
    exact mul_pos ha0 hlog0
  have hx_le : x ≤ Real.log 3 := by
    rw [hxdef]
    have h := mul_le_mul_of_nonneg_right ha1 hlog0.le
    simpa using h
  have hxa : a ≤ x := by
    rw [hxdef]
    have h := mul_le_mul_of_nonneg_left hlog.le ha0.le
    simpa using h
  have hrpow : (3 : ℝ) ^ (-a) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    dsimp only [x]
    ring
  have hexp_log3 : Real.exp (-(Real.log 3)) = (1 : ℝ) / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3), one_div]
  have hexp_lower : (1 : ℝ) / 3 ≤ Real.exp (-x) := by
    rw [← hexp_log3]
    exact Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hxle : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hkey : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
    calc x * Real.exp (-x) ≤ (Real.exp x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hxle (Real.exp_pos (-x)).le
      _ = 1 - Real.exp (-x) := by rw [sub_mul, one_mul, he]
  have hmul2 : a * (1 / 3) ≤ x * Real.exp (-x) :=
    mul_le_mul hxa hexp_lower (by norm_num) hx_pos.le
  have ha3 : a / 3 ≤ 1 - Real.exp (-x) := by
    have h1 : a / 3 = a * (1 / 3) := by ring
    rw [h1]
    exact hmul2.trans hkey
  have hmain : a / 3 ≤ 1 - (3 : ℝ) ^ (-a) := by
    rw [hrpow]
    exact ha3
  have hden : 0 < a / 3 := by positivity
  calc (1 - (3 : ℝ) ^ (-a))⁻¹ = 1 / (1 - (3 : ℝ) ^ (-a)) := by
        rw [div_eq_mul_inv, one_mul]
    _ ≤ 1 / (a / 3) := one_div_le_one_div_of_le hden hmain
    _ = 3 / a := by rw [one_div_div]

/-- At `a = 1/2` the reciprocal bound sharpens to `3`. -/
theorem h6a_inv_one_sub_rpow_half_le : (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ ≤ 3 := by
  have hsq : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 : ℝ) / 3 := by
    rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (-(1 / 2 : ℝ)) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  have hle : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ ((2 : ℝ) / 3) ^ 2 := by
    rw [hsq]
    norm_num
  have hr : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) / 3 :=
    le_of_sq_le_sq hle (by norm_num)
  have hden : (1 : ℝ) / 3 ≤ 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
  have hpos : 0 < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
  rw [inv_le_iff_one_le_mul₀' hpos]
  nlinarith [hden]

end

end Homogenization.HighContrast.Multiscale
