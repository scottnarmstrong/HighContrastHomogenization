/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.RoundedHops

/-!
# Post-termination witness and grid bounds

After the transition count is known, the accumulated projective path gives
the absolute witness radius.  The rounded-grid estimate then turns that radius
into the polynomial grid-ratio bound returned by the selector.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

/-- The polynomial exponent for the terminal witness eccentricity. -/
def radiusExponent (chop CN : ℝ) : ℝ :=
  chop * CN / Real.log 3

/-- Defining equation for the terminal radius exponent. -/
theorem radiusExponent_eq (chop CN : ℝ) :
    radiusExponent chop CN = chop * CN / Real.log 3 := rfl

/-- The polynomial exponent for the terminal rounded-grid ratio. -/
def gridExponent (d : ℕ) (chop CN : ℝ) : ℝ :=
  2 * (d : ℝ) * radiusExponent chop CN +
    Real.logb 3 (witnessGridConstant d * (4 : ℝ) ^ d)

/-- Defining equation for the terminal grid exponent. -/
theorem gridExponent_eq (d : ℕ) (chop CN : ℝ) :
    gridExponent d chop CN =
      2 * (d : ℝ) * radiusExponent chop CN +
        Real.logb 3 (witnessGridConstant d * (4 : ℝ) ^ d) := rfl

/-- The terminal radius exponent is positive. -/
theorem radiusExponent_pos {chop CN : ℝ} (hchop : 0 < chop) (hCN : 0 < CN) :
    0 < radiusExponent chop CN := by
  rw [radiusExponent_eq]
  exact div_pos (mul_pos hchop hCN) (Real.log_pos (by norm_num))

/-- The terminal grid exponent is positive in every nonzero dimension. -/
theorem gridExponent_pos {d : ℕ} (hd : 1 ≤ d) {chop CN : ℝ}
    (hchop : 0 < chop) (hCN : 0 < CN) :
    0 < gridExponent d chop CN := by
  have hrad := radiusExponent_pos hchop hCN
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hfirst : 0 < 2 * (d : ℝ) * radiusExponent chop CN := by positivity
  have hconst : 1 ≤ witnessGridConstant d * (4 : ℝ) ^ d := by
    rw [witnessGridConstant_eq]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hlog : 0 ≤ Real.logb 3 (witnessGridConstant d * (4 : ℝ) ^ d) :=
    Real.logb_nonneg (by norm_num) hconst
  rw [gridExponent_eq]
  exact add_pos_of_pos_of_nonneg hfirst hlog

/-- A projective path with at most `C_N Λ` hops gives the printed polynomial
witness-eccentricity bound. -/
theorem witnessEccentricity_le_rpow_of_hopCount {d Nhop : ℕ} (hd : 1 ≤ d)
    {chop CN Pi Lam : ℝ} {m : Mat d} (hm : m.PosDef)
    (hchop : 0 ≤ chop) (hPi : 1 ≤ Pi)
    (hLam : Lam = Real.logb 3 (2 + Pi))
    (hproj : projDist 1 m ≤ chop * (Nhop : ℝ))
    (hcount : (Nhop : ℝ) ≤ CN * Lam) :
    witnessEccentricity m ≤ (2 + Pi) ^ radiusExponent chop CN := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  let base : ℝ := 2 + Pi
  have hbase0 : 0 < base := by dsimp [base]; linarith only [hPi]
  have hpath : projDist 1 m ≤ chop * (CN * Lam) :=
    hproj.trans (mul_le_mul_of_nonneg_left hcount hchop)
  have hexponent : chop * (CN * Lam) =
      Real.log base * radiusExponent chop CN := by
    rw [hLam, radiusExponent_eq]
    dsimp [base, Real.logb]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
  rw [rounded_witnessEccentricity_eq_exp hm, Real.rpow_def_of_pos hbase0]
  exact Real.exp_le_exp.mpr (hpath.trans_eq hexponent)

/-- The rounded-grid witness bound and the eccentricity estimate give the
printed terminal grid-ratio exponent. -/
theorem gridRatio_roundedGrid_one_le_rpow {d : ℕ} (hd : 2 ≤ d) {jStar : ℤ}
    (hjStar : (kZero d : ℤ) ≤ jStar) {chop CN Pi : ℝ} {m : Mat d}
    (hm : m.PosDef) (hPi : 1 ≤ Pi)
    (hecc : witnessEccentricity m ≤ (2 + Pi) ^ radiusExponent chop CN) :
    gridRatio (roundedGrid jStar m) 1 ≤ (2 + Pi) ^ gridExponent d chop CN := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  let base : ℝ := 2 + Pi
  let e : ℝ := witnessEccentricity m
  let K : ℝ := witnessGridConstant d * (4 : ℝ) ^ d
  have hbase3 : 3 ≤ base := by dsimp [base]; linarith only [hPi]
  have hbase0 : 0 < base := lt_of_lt_of_le (by norm_num) hbase3
  have hbase1 : 1 ≤ base := (by norm_num : (1 : ℝ) ≤ 3).trans hbase3
  have he1 : 1 ≤ e := by
    dsimp [e]
    rw [rounded_witnessEccentricity_eq_exp hm]
    exact Real.one_le_exp (projDist_nonneg Matrix.PosDef.one hm)
  have hsum : 1 + e ≤ 2 * (base ^ radiusExponent chop CN) := by
    have : 1 + e ≤ 2 * e := by linarith only [he1]
    exact this.trans (mul_le_mul_of_nonneg_left
      (by simpa only [base, e] using hecc) (by norm_num))
  have hpow : (1 + e) ^ (2 * d) ≤
      (2 * (base ^ radiusExponent chop CN)) ^ (2 * d) :=
    pow_le_pow_left₀ (by linarith only [he1]) hsum _
  have htwo : (2 : ℝ) ^ (2 * d) = (4 : ℝ) ^ d := by
    rw [pow_mul]
    norm_num
  have hradPow : (base ^ radiusExponent chop CN) ^ (2 * d) =
      base ^ (2 * (d : ℝ) * radiusExponent chop CN) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0.le]
    push_cast
    congr 1
    ring
  have hexpand : witnessGridConstant d *
        (2 * (base ^ radiusExponent chop CN)) ^ (2 * d) =
      K * base ^ (2 * (d : ℝ) * radiusExponent chop CN) := by
    dsimp [K]
    rw [mul_pow, htwo, hradPow]
    ring
  have hKpos : 0 < K := by dsimp [K, witnessGridConstant]; positivity
  have hKone : 1 ≤ K := by
    dsimp [K]
    rw [witnessGridConstant_eq]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hlogK : 0 ≤ Real.logb 3 K := Real.logb_nonneg (by norm_num) hKone
  have hKbase : K ≤ base ^ Real.logb 3 K := by
    have hmono := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 3) hbase3 hlogK
    rw [Real.rpow_logb (by norm_num) (by norm_num) hKpos] at hmono
    exact hmono
  have hgrid := gridRatio_roundedGrid_one_le hd hjStar hm
  calc
    gridRatio (roundedGrid jStar m) 1
        ≤ witnessGridConstant d * (1 + e) ^ (2 * d) := by
      simpa only [e] using hgrid
    _ ≤ witnessGridConstant d *
          (2 * (base ^ radiusExponent chop CN)) ^ (2 * d) :=
      mul_le_mul_of_nonneg_left hpow (by dsimp [witnessGridConstant]; positivity)
    _ = K * base ^ (2 * (d : ℝ) * radiusExponent chop CN) := hexpand
    _ ≤ base ^ Real.logb 3 K *
          base ^ (2 * (d : ℝ) * radiusExponent chop CN) :=
      mul_le_mul_of_nonneg_right hKbase (Real.rpow_nonneg hbase0.le _)
    _ = base ^ gridExponent d chop CN := by
      rw [← Real.rpow_add hbase0]
      dsimp [gridExponent, K]
      congr 1
      ring

end

end Selection
end HighContrast
end Homogenization
