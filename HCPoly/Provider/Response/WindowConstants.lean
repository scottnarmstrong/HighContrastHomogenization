/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.Exponents

/-!
# The constants of the response window

The response window fixes, once and before any coefficient law, a tuple of
scalars: the two universal constants of the response estimate and its nine
calibration, energy and profile constants, which are built from the determinant
slack `R = 1 + δ_det` alone:
```
c_const := (1 - 3^{-1/2})^{-1},  Γ_* := 2/(1 - 3^{-3/2}) + 1,  c_{ε,*} := √2,
β_* := c_{ε,*}R^{d/2},  χ_θ := √(3/2)R^{d/2},  A_* := 2χ_θ,
T_* := 2(R^d - 1)χ_θ,   L_* := 32Γ_*c_{ε,*}β_*R^{d/2}χ_θ,
K_* := β_*^{1/2}R^{d/4},  L_{en,*} := 2χ_θ^{1/2},  Λ_* := √5 χ_θ^{1/2}.
```

This module records the two facts the numerical absorption closing the response
estimate uses about them.  On the admissible range `0 < δ_det ≤ 1` of
`e.response.transfer.tolerances` every one of the nine is bounded above by an
explicit power of `2^d` *uniformly in
`δ_det`* — the slack enters the printed formulas only through `R^{d/2}`,
`R^{d/4}` and `R^d`, all in `[1, 2^d]`; and the single constant that must be
made small, `T_*`, is at most `4·(2^d)^2·δ_det`, so it vanishes linearly as
`δ_det ↓ 0`, which is the first of the three limits fixing the finite-window
summation coefficients.

No definitions are carried: each constant is read off its printed defining
equation, passed as a hypothesis, as the argument of
`e.response.adapted.conclusion` will read it.  The scalar tools at the head are
the three thresholds the three limits need — a square-root comparison, a
geometric-decay threshold in a natural exponent (`H ↑ ∞`) and a power threshold
in a positive real exponent (`η ↓ 0`).
-/

namespace Homogenization
namespace HighContrast
namespace Response

noncomputable section

/-! ## Scalar tools -/

/-- A square root is below any nonnegative bound whose square dominates. -/
theorem sqrt_le_of_sq_le {x c : ℝ} (hc : 0 ≤ c) (h : x ≤ c ^ 2) : Real.sqrt x ≤ c := by
  calc Real.sqrt x ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

/-- The chord bound `(1+δ)^n ≤ 1 + δ(2^n - 1)` on the unit slack range. -/
theorem one_add_pow_le {delta : ℝ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) (n : ℕ) :
    (1 + delta) ^ n ≤ 1 + delta * ((2 : ℝ) ^ n - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      have hbase : (0 : ℝ) ≤ 1 + delta := by linarith only [h0]
      have hstep : (1 + delta) ^ (m + 1) ≤ (1 + delta * ((2 : ℝ) ^ m - 1)) * (1 + delta) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih hbase
      have hsq : delta * delta ≤ delta := by nlinarith only [h0, h1]
      have hprod : delta * delta * ((2 : ℝ) ^ m - 1) ≤ delta * ((2 : ℝ) ^ m - 1) :=
        mul_le_mul_of_nonneg_right hsq (by linarith only [hpow])
      have hexp : (1 + delta * ((2 : ℝ) ^ m - 1)) * (1 + delta)
          = 1 + delta * (2 * (2 : ℝ) ^ m - 1) +
            (delta * delta * ((2 : ℝ) ^ m - 1) - delta * ((2 : ℝ) ^ m - 1)) := by ring
      have hgoal : (1 : ℝ) + delta * ((2 : ℝ) ^ (m + 1) - 1)
          = 1 + delta * (2 * (2 : ℝ) ^ m - 1) := by rw [pow_succ]; ring
      rw [hgoal]
      linarith only [hstep, hexp, hprod]

/-- On the unit slack range the determinant factor `R^e = (1+δ)^e` is at most
`2^d` for every exponent `e` between `0` and `d`. -/
theorem rpow_one_add_le {delta e : ℝ} {d : ℕ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1)
    (he0 : 0 ≤ e) (hed : e ≤ (d : ℝ)) : (1 + delta) ^ e ≤ (2 : ℝ) ^ d := by
  calc (1 + delta) ^ e ≤ (2 : ℝ) ^ e :=
        Real.rpow_le_rpow (by linarith only [h0]) (by linarith only [h1]) he0
    _ ≤ (2 : ℝ) ^ ((d : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hed
    _ = (2 : ℝ) ^ d := Real.rpow_natCast 2 d

/-- The determinant factor is at least one. -/
theorem one_le_rpow_one_add {delta e : ℝ} (h0 : 0 ≤ delta) (he0 : 0 ≤ e) :
    1 ≤ (1 + delta) ^ e :=
  Real.one_le_rpow (by linarith only [h0]) he0

/-- The squared determinant factor `R^{2d}` of the numerical absorption is at
most `(2^d)^2`. -/
theorem rpow_one_add_two_mul_le {delta : ℝ} {d : ℕ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    (1 + delta) ^ (2 * (d : ℝ)) ≤ ((2 : ℝ) ^ d) ^ 2 := by
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hcast : 2 * (d : ℝ) = ((2 * d : ℕ) : ℝ) := by push_cast; ring
  calc (1 + delta) ^ (2 * (d : ℝ)) ≤ (2 : ℝ) ^ (2 * (d : ℝ)) :=
        Real.rpow_le_rpow (by linarith only [h0]) (by linarith only [h1]) hd0
    _ = (2 : ℝ) ^ (2 * d) := by rw [hcast, Real.rpow_natCast]
    _ = ((2 : ℝ) ^ d) ^ 2 := by rw [pow_mul']

/-- The determinant excess `R^d - 1` vanishes linearly with the slack. -/
theorem rpow_one_add_sub_one_le {delta : ℝ} {d : ℕ} (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    (1 + delta) ^ (d : ℝ) - 1 ≤ delta * (2 : ℝ) ^ d := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hchord := one_add_pow_le h0 h1 d
  have hcast : (1 + delta) ^ (d : ℝ) = (1 + delta) ^ d := Real.rpow_natCast _ d
  nlinarith only [hchord, hcast, hpow, h0]

/-- A geometric decay in a natural exponent falls below any positive threshold,
and stays there.  This is the `H ↑ ∞` limit in the choice of the finite-window
summation coefficients. -/
theorem exists_nat_forall_mul_pow_le {c r target : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (ht : 0 < target) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * r ^ n ≤ target := by
  have hc1 : (0 : ℝ) < c + 1 := by linarith only [hc]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ht hc1) hr1
  refine ⟨N, fun n hn => ?_⟩
  have hmono : r ^ n ≤ r ^ N := pow_le_pow_of_le_one hr0 (le_of_lt hr1) hn
  have hle : r ^ n ≤ target / (c + 1) := le_trans hmono (le_of_lt hN)
  have hstep : c * r ^ n ≤ c * (target / (c + 1)) :=
    mul_le_mul_of_nonneg_left hle hc
  have hfin : c * (target / (c + 1)) ≤ target := by
    rw [mul_div_assoc', div_le_iff₀ hc1]
    nlinarith only [ht, hc]
  linarith only [hstep, hfin]

/-- A positive real power of the smallness parameter falls below any positive
threshold inside the admissible range `(0, 1/2]` of the choice order.  This is
the `η ↓ 0` limit in the choice of the finite-window summation coefficients. -/
theorem exists_eta_mul_rpow_le {c r p : ℝ} (hc : 0 ≤ c) (hr : 0 < r) (hp : 0 < p) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 / 2 ∧ c * eta ^ p ≤ r := by
  have hc1 : (0 : ℝ) < c + 1 := by linarith only [hc]
  have hu0 : (0 : ℝ) < min 1 (r / (c + 1)) := lt_min zero_lt_one (div_pos hr hc1)
  have hur : min 1 (r / (c + 1)) ≤ r / (c + 1) := min_le_right _ _
  have hpos : (0 : ℝ) < min (1 / 2) (min 1 (r / (c + 1)) ^ p⁻¹) :=
    lt_min (by norm_num) (Real.rpow_pos_of_pos hu0 _)
  refine ⟨min (1 / 2) (min 1 (r / (c + 1)) ^ p⁻¹), hpos, min_le_left _ _, ?_⟩
  have hstep : (min (1 / 2) (min 1 (r / (c + 1)) ^ p⁻¹)) ^ p ≤
      (min 1 (r / (c + 1)) ^ p⁻¹) ^ p :=
    Real.rpow_le_rpow hpos.le (min_le_right _ _) hp.le
  have hcollapse : (min 1 (r / (c + 1)) ^ p⁻¹) ^ p = min 1 (r / (c + 1)) := by
    rw [← Real.rpow_mul hu0.le, inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  have hle : (min (1 / 2) (min 1 (r / (c + 1)) ^ p⁻¹)) ^ p ≤ r / (c + 1) := by
    rw [hcollapse] at hstep
    exact le_trans hstep hur
  have hmul : c * (min (1 / 2) (min 1 (r / (c + 1)) ^ p⁻¹)) ^ p ≤ c * (r / (c + 1)) :=
    mul_le_mul_of_nonneg_left hle hc
  have hfin : c * (r / (c + 1)) ≤ r := by
    rw [mul_div_assoc', div_le_iff₀ hc1]
    nlinarith only [hr, hc]
  linarith only [hmul, hfin]

/-! ## The two universal constants -/

/-- A universal constant of the response estimate: the geometric constant
`c_const = (1 - 3^{-1/2})^{-1}` lies between one and three. -/
theorem cconst_bounds {cconst : ℝ} (h : cconst = (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) :
    1 ≤ cconst ∧ cconst ≤ 3 := by
  have hsq : (3 : ℝ) ^ (-(1 / 2) : ℝ) * (3 : ℝ) ^ (-(1 / 2) : ℝ) = 3⁻¹ := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (3 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 / 3 := by nlinarith only [hsq, hpos]
  have hden : (1 : ℝ) / 3 ≤ 1 - (3 : ℝ) ^ (-(1 / 2) : ℝ) := by linarith only [hlt]
  have hden1 : 1 - (3 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 := by linarith only [hpos]
  have hdenpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 2) : ℝ) := by linarith only [hden]
  constructor
  · rw [h, le_inv_comm₀ zero_lt_one hdenpos, inv_one]
    exact hden1
  · rw [h, inv_le_comm₀ hdenpos (by norm_num)]
    linarith only [hden]

/-- A universal constant of the response estimate: the row constant
`Γ_* = 2/(1 - 3^{-3/2}) + 1` lies between one and four. -/
theorem gammaStar_bounds {GammaStar : ℝ}
    (h : GammaStar = 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1) :
    1 ≤ GammaStar ∧ GammaStar ≤ 4 := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (3 : ℝ) ^ (-(3 / 2) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hthird : (3 : ℝ) ^ (-(3 / 2) : ℝ) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hthird' : (3 : ℝ) ^ (-1 : ℝ) = 3⁻¹ := Real.rpow_neg_one 3
  have hden : (2 : ℝ) / 3 ≤ 1 - (3 : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [hthird'] at hthird
    linarith only [hthird]
  have hdenpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(3 / 2) : ℝ) := by linarith only [hlt]
  have hfrac : 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) ≤ 3 := by
    rw [div_le_iff₀ hdenpos]
    linarith only [hden]
  have hfrac0 : (0 : ℝ) ≤ 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) :=
    le_of_lt (div_pos (by norm_num) hdenpos)
  exact ⟨by rw [h]; linarith only [hfrac0], by rw [h]; linarith only [hfrac]⟩

/-! ## The nine slack constants, uniformly on `0 < δ_det ≤ 1` -/

/-- A calibration constant of the response estimate: `χ_θ = √(3/2)R^{d/2}` lies
between one and `2·2^d`. -/
theorem chiTheta_bounds {d : ℕ} {deltaDet chiTheta : ℝ} (h0 : 0 ≤ deltaDet)
    (h1 : deltaDet ≤ 1)
    (h : chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2)) :
    1 ≤ chiTheta ∧ chiTheta ≤ 2 * (2 : ℝ) ^ d := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdN : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdd : (d : ℝ) / 2 ≤ (d : ℝ) := by linarith only [hdN]
  have hR1 : 1 ≤ (1 + deltaDet) ^ ((d : ℝ) / 2) := one_le_rpow_one_add h0 hd0
  have hR2 : (1 + deltaDet) ^ ((d : ℝ) / 2) ≤ (2 : ℝ) ^ d := rpow_one_add_le h0 h1 hd0 hdd
  have hs1 : (1 : ℝ) ≤ Real.sqrt (3 / 2) := Real.one_le_sqrt.mpr (by norm_num)
  have hs2 : Real.sqrt (3 / 2) ≤ 2 := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  constructor
  · rw [h]; nlinarith only [hs1, hR1]
  · rw [h]; nlinarith only [hs1, hs2, hR1, hR2]

/-- A calibration constant of the response estimate: `β_* = √2 R^{d/2}` lies
between one and `2·2^d`. -/
theorem betaStar_bounds {d : ℕ} {deltaDet cepsStar betaStar : ℝ} (h0 : 0 ≤ deltaDet)
    (h1 : deltaDet ≤ 1) (hc : cepsStar = Real.sqrt 2)
    (h : betaStar = cepsStar * (1 + deltaDet) ^ ((d : ℝ) / 2)) :
    1 ≤ betaStar ∧ betaStar ≤ 2 * (2 : ℝ) ^ d := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdN : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdd : (d : ℝ) / 2 ≤ (d : ℝ) := by linarith only [hdN]
  have hR1 : 1 ≤ (1 + deltaDet) ^ ((d : ℝ) / 2) := one_le_rpow_one_add h0 hd0
  have hR2 : (1 + deltaDet) ^ ((d : ℝ) / 2) ≤ (2 : ℝ) ^ d := rpow_one_add_le h0 h1 hd0 hdd
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ≤ 2 := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  constructor
  · rw [h, hc]; nlinarith only [hs1, hR1]
  · rw [h, hc]; nlinarith only [hs1, hs2, hR1, hR2]

/-- An energy constant of the response estimate: `A_* = 2χ_θ` lies between two
and `4·2^d`. -/
theorem aStar_bounds {d : ℕ} {deltaDet chiTheta AStar : ℝ} (h0 : 0 ≤ deltaDet)
    (h1 : deltaDet ≤ 1)
    (hx : chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
    (h : AStar = 2 * chiTheta) :
    2 ≤ AStar ∧ AStar ≤ 4 * (2 : ℝ) ^ d := by
  obtain ⟨hlo, hhi⟩ := chiTheta_bounds h0 h1 hx
  exact ⟨by rw [h]; linarith only [hlo], by rw [h]; linarith only [hhi]⟩

/-- An energy constant of the response estimate: `T_* = 2(R^d - 1)χ_θ` is
nonnegative and vanishes linearly with the determinant slack.  This is the first
of the three limits fixing the finite-window summation coefficients. -/
theorem tStar_bounds {d : ℕ} {deltaDet chiTheta TStar : ℝ} (h0 : 0 ≤ deltaDet)
    (h1 : deltaDet ≤ 1)
    (hx : chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
    (h : TStar = 2 * ((1 + deltaDet) ^ (d : ℝ) - 1) * chiTheta) :
    0 ≤ TStar ∧ TStar ≤ 4 * ((2 : ℝ) ^ d) ^ 2 * deltaDet := by
  obtain ⟨hlo, hhi⟩ := chiTheta_bounds h0 h1 hx
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hR1 : 1 ≤ (1 + deltaDet) ^ (d : ℝ) := one_le_rpow_one_add h0 hd0
  have hexc : (1 + deltaDet) ^ (d : ℝ) - 1 ≤ deltaDet * (2 : ℝ) ^ d :=
    rpow_one_add_sub_one_le h0 h1
  have hMpos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  constructor
  · rw [h]; nlinarith only [hlo, hR1]
  · rw [h]; nlinarith only [hlo, hhi, hR1, hexc, hMpos, h0]

/-- An energy constant of the response estimate:
`L_* = 32Γ_*c_{ε,*}β_*R^{d/2}χ_θ` is nonnegative and at most `1024·(2^d)^3`. -/
theorem lStar_bounds {d : ℕ} {deltaDet GammaStar cepsStar betaStar chiTheta LStar : ℝ}
    (h0 : 0 ≤ deltaDet) (h1 : deltaDet ≤ 1)
    (hG : GammaStar = 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1)
    (hc : cepsStar = Real.sqrt 2)
    (hb : betaStar = cepsStar * (1 + deltaDet) ^ ((d : ℝ) / 2))
    (hx : chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
    (h : LStar =
      32 * GammaStar * cepsStar * betaStar * (1 + deltaDet) ^ ((d : ℝ) / 2) * chiTheta) :
    0 ≤ LStar ∧ LStar ≤ 1024 * ((2 : ℝ) ^ d) ^ 3 := by
  obtain ⟨hGlo, hGhi⟩ := gammaStar_bounds hG
  obtain ⟨hblo, hbhi⟩ := betaStar_bounds h0 h1 hc hb
  obtain ⟨hxlo, hxhi⟩ := chiTheta_bounds h0 h1 hx
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdN : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdd : (d : ℝ) / 2 ≤ (d : ℝ) := by linarith only [hdN]
  have hR1 : 1 ≤ (1 + deltaDet) ^ ((d : ℝ) / 2) := one_le_rpow_one_add h0 hd0
  have hR2 : (1 + deltaDet) ^ ((d : ℝ) / 2) ≤ (2 : ℝ) ^ d := rpow_one_add_le h0 h1 hd0 hdd
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ≤ 2 := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  rw [h, hc]
  refine ⟨by positivity, ?_⟩
  have e1 : 32 * GammaStar ≤ 32 * 4 := by linarith only [hGhi]
  have e2 : 32 * GammaStar * Real.sqrt 2 ≤ 32 * 4 * 2 :=
    mul_le_mul e1 hs2 (Real.sqrt_nonneg 2) (by norm_num)
  have e3 : 32 * GammaStar * Real.sqrt 2 * betaStar ≤ 32 * 4 * 2 * (2 * (2 : ℝ) ^ d) :=
    mul_le_mul e2 hbhi (by linarith only [hblo]) (by norm_num)
  have e4 : 32 * GammaStar * Real.sqrt 2 * betaStar * (1 + deltaDet) ^ ((d : ℝ) / 2) ≤
      32 * 4 * 2 * (2 * (2 : ℝ) ^ d) * (2 : ℝ) ^ d :=
    mul_le_mul e3 hR2 (by linarith only [hR1]) (by nlinarith only [hM1])
  calc 32 * GammaStar * Real.sqrt 2 * betaStar * (1 + deltaDet) ^ ((d : ℝ) / 2) * chiTheta
      ≤ 32 * 4 * 2 * (2 * (2 : ℝ) ^ d) * (2 : ℝ) ^ d * (2 * (2 : ℝ) ^ d) :=
        mul_le_mul e4 hxhi (by linarith only [hxlo]) (by nlinarith only [hM1])
    _ = 1024 * ((2 : ℝ) ^ d) ^ 3 := by ring

/-- A profile constant of the response estimate: `K_* = β_*^{1/2}R^{d/4}` lies
between one and `2·(2^d)^2`. -/
theorem kStar_bounds {d : ℕ} {deltaDet cepsStar betaStar KStar : ℝ} (h0 : 0 ≤ deltaDet)
    (h1 : deltaDet ≤ 1) (hc : cepsStar = Real.sqrt 2)
    (hb : betaStar = cepsStar * (1 + deltaDet) ^ ((d : ℝ) / 2))
    (h : KStar = Real.sqrt betaStar * (1 + deltaDet) ^ ((d : ℝ) / 4)) :
    1 ≤ KStar ∧ KStar ≤ 2 * ((2 : ℝ) ^ d) ^ 2 := by
  obtain ⟨hblo, hbhi⟩ := betaStar_bounds h0 h1 hc hb
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 4 := by positivity
  have hdN : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdd : (d : ℝ) / 4 ≤ (d : ℝ) := by linarith only [hdN]
  have hR1 : 1 ≤ (1 + deltaDet) ^ ((d : ℝ) / 4) := one_le_rpow_one_add h0 hd0
  have hR2 : (1 + deltaDet) ^ ((d : ℝ) / 4) ≤ (2 : ℝ) ^ d := rpow_one_add_le h0 h1 hd0 hdd
  have hslo : (1 : ℝ) ≤ Real.sqrt betaStar := Real.one_le_sqrt.mpr hblo
  have hshi : Real.sqrt betaStar ≤ betaStar :=
    sqrt_le_of_sq_le (by linarith only [hblo]) (by nlinarith only [hblo])
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  constructor
  · rw [h]; nlinarith only [hslo, hR1]
  · rw [h]; nlinarith only [hslo, hshi, hbhi, hR1, hR2, hM1]

/-- A profile constant of the response estimate: `L_{en,*} = 2χ_θ^{1/2}` lies
between two and `4·2^d`. -/
theorem lenStar_bounds {d : ℕ} {deltaDet chiTheta LenStar : ℝ} (h0 : 0 ≤ deltaDet)
    (h1 : deltaDet ≤ 1)
    (hx : chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
    (h : LenStar = 2 * Real.sqrt chiTheta) :
    2 ≤ LenStar ∧ LenStar ≤ 4 * (2 : ℝ) ^ d := by
  obtain ⟨hxlo, hxhi⟩ := chiTheta_bounds h0 h1 hx
  have hslo : (1 : ℝ) ≤ Real.sqrt chiTheta := Real.one_le_sqrt.mpr hxlo
  have hshi : Real.sqrt chiTheta ≤ chiTheta :=
    sqrt_le_of_sq_le (by linarith only [hxlo]) (by nlinarith only [hxlo])
  exact ⟨by rw [h]; linarith only [hslo],
    by rw [h]; linarith only [hshi, hxhi]⟩

/-- A profile constant of the response estimate: `Λ_* = √5 χ_θ^{1/2}` is
nonnegative and at most `6·2^d`. -/
theorem lambdaStar_bounds {d : ℕ} {deltaDet chiTheta LambdaStar : ℝ} (h0 : 0 ≤ deltaDet)
    (h1 : deltaDet ≤ 1)
    (hx : chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
    (h : LambdaStar = Real.sqrt 5 * Real.sqrt chiTheta) :
    0 ≤ LambdaStar ∧ LambdaStar ≤ 6 * (2 : ℝ) ^ d := by
  obtain ⟨hxlo, hxhi⟩ := chiTheta_bounds h0 h1 hx
  have hslo : (1 : ℝ) ≤ Real.sqrt chiTheta := Real.one_le_sqrt.mpr hxlo
  have hshi : Real.sqrt chiTheta ≤ chiTheta :=
    sqrt_le_of_sq_le (by linarith only [hxlo]) (by nlinarith only [hxlo])
  have h5lo : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5hi : Real.sqrt 5 ≤ 3 := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  exact ⟨by rw [h]; positivity,
    by rw [h]; nlinarith only [h5lo, h5hi, hslo, hshi, hxhi]⟩

end

end Response
end HighContrast
end Homogenization
