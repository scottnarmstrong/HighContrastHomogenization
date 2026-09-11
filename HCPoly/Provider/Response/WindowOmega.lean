/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.WindowConstants

/-!
# The response coefficient `ω_rsp` and the closing contradiction

The coefficient of the sum of the two terminal responses,
```
ω_rsp(H,η,δ_det) := 2C_d(T_* + √(T_*A_*) + √(T_*L_*)
                        + 3^{-H}(A_* + √(A_*L_*)) + 𝓡_*(H,η)^2),
```
is read here in two halves.  `rStar_le_sqrt` bounds the weak-norm constant of
the response estimate,
```
𝓡_* := C_dK_*L_{en,*}U_* + C_dK_*√2Λ_*(2a)^{-1}(B_* + 3^{-aH})
        + c_const K_*L_{en,*}η^{1/Q}
```
by `√s` once the three coefficients are below a common majorant `W` and the two
thresholds — one in `H`, one in `η` — are met; the recent-window constant and
the bad-event constant enter only through the single power
`η^{1/(2Q)}`, which dominates `η^{1/Q}` and `η^{1/2}` on `0 < η ≤ 1`, and no
sign condition on `1/2 - ρ_max` is used.  `omega_le_of_slack` then bounds each
of the five summands of `ω_rsp` by `s` and concludes `ω_rsp ≤ 10C_ds`.

`imbalance_le_of_absorption` is the closing step: with the
canonical comparison `κ_s ≤ R^{2d}κ_t` at the two response endpoints, the
normalized response defect and the factor-twelve bound for the terminal
imbalance, the numerical absorption closing the response estimate forces
`κ_t ≤ 1 + δ_ad`.
-/

namespace Homogenization
namespace HighContrast
namespace Response

noncomputable section

/-- The coefficient `ω_rsp` of the two terminal responses is nonnegative as soon
as the two constants it reads through a square root are; `expo` is the
lower-edge factor `3^{-H}`. -/
theorem omegaRsp_nonneg {Cd TStar AStar LStar RStar expo omegaRsp : ℝ} (hCd : 0 ≤ Cd)
    (hT : 0 ≤ TStar) (hA : 0 ≤ AStar) (hexpo : 0 ≤ expo)
    (homega : omegaRsp = 2 * Cd * (TStar + Real.sqrt (TStar * AStar) +
      Real.sqrt (TStar * LStar) + expo * (AStar + Real.sqrt (AStar * LStar)) +
      RStar ^ 2)) :
    0 ≤ omegaRsp := by
  have q1 : (0 : ℝ) ≤ Real.sqrt (TStar * AStar) := Real.sqrt_nonneg _
  have q2 : (0 : ℝ) ≤ Real.sqrt (TStar * LStar) := Real.sqrt_nonneg _
  have q3 : (0 : ℝ) ≤ expo * (AStar + Real.sqrt (AStar * LStar)) :=
    mul_nonneg hexpo (by linarith only [hA, Real.sqrt_nonneg (AStar * LStar)])
  have hsum : (0 : ℝ) ≤ TStar + Real.sqrt (TStar * AStar) + Real.sqrt (TStar * LStar) +
      expo * (AStar + Real.sqrt (AStar * LStar)) + RStar ^ 2 := by
    linarith only [hT, q1, q2, q3, sq_nonneg RStar]
  rw [homega]
  exact mul_nonneg (by linarith only [hCd]) hsum

/-- **The weak-norm constant of the response estimate** below `√s`.
The three coefficients are bounded by the common majorant `W`, the recent and
bad constants collapse onto the single power `η^{1/(2Q)}` and the two remaining
thresholds — the lower-edge row `W3^{-aH} ≤ √s/2` and the smallness
`W(S+2^{Q/2}+1)η^{1/(2Q)} ≤ √s/2` — close it.  This is the `η ↓ 0` half of the
choice of the finite-window summation coefficients. -/
theorem rStar_le_sqrt {d : ℕ} (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {Cd cconst KStar LenStar LambdaStar Scen Scell Sav Sfull UStar BStar RStar W
      eta s : ℝ} {H : ℕ}
    (hCd : 1 ≤ Cd) (hcc1 : 1 ≤ cconst) (hcc3 : cconst ≤ 3)
    (hK1 : 1 ≤ KStar) (hK2 : KStar ≤ 2 * ((2 : ℝ) ^ d) ^ 2)
    (hLen1 : 2 ≤ LenStar) (hLen2 : LenStar ≤ 4 * (2 : ℝ) ^ d)
    (hLam1 : 0 ≤ LambdaStar) (hLam2 : LambdaStar ≤ 6 * (2 : ℝ) ^ d)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 2) (hs : 0 < s)
    (hW0 : 0 ≤ W) (hW1 : 8 * Cd * ((2 : ℝ) ^ d) ^ 3 ≤ W)
    (hW2 : 24 * ((2 : ℝ) ^ d) ^ 3 ≤ W)
    (hW3 : 24 * Cd * ((2 : ℝ) ^ d) ^ 3 ≤ W * (2 * initExpA g))
    (hScen0 : 0 ≤ Scen) (hScell0 : 0 ≤ Scell) (hSav0 : 0 ≤ Sav)
    (hSsum : Scen + Scell + Sav = Sfull)
    (hUstar : UStar = (Scen + Scell) * eta ^ ((initExpQ d g : ℝ)⁻¹) +
      Sav * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹))
    (hBstar : BStar = (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) * eta ^ ((2 : ℝ)⁻¹))
    (hRstar : RStar = Cd * KStar * LenStar * UStar +
      Cd * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
        (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) +
      cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹))
    (hHrow : W * ((3 : ℝ) ^ (-initExpA g)) ^ H ≤ Real.sqrt s / 2)
    (hetakey : W * (Sfull + (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) + 1) *
      eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) ≤ Real.sqrt s / 2) :
    0 ≤ RStar ∧ RStar ^ 2 ≤ s := by
  have hQpos : (0 : ℝ) < (initExpQ d g : ℝ) := zero_lt_initExpQ hd hg
  have hQ12 : (12 : ℝ) ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast twelve_le_initExpQ hd hg
  have ha : 0 < initExpA g := zero_lt_initExpA hg
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hM0 : (0 : ℝ) ≤ (2 : ℝ) ^ d := le_trans zero_le_one hM1
  have hetaLe1 : eta ≤ 1 := by linarith only [heta1]
  have hinvQ : (2 * (initExpQ d g : ℝ))⁻¹ ≤ ((initExpQ d g : ℝ))⁻¹ := by
    rw [inv_le_inv₀ (by linarith only [hQpos]) hQpos]
    linarith only [hQpos]
  have hinv2 : (2 * (initExpQ d g : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ (by linarith only [hQpos]) (by norm_num)]
    linarith only [hQ12]
  have hqle : eta ^ ((initExpQ d g : ℝ)⁻¹) ≤ eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) :=
    Real.rpow_le_rpow_of_exponent_ge heta0 hetaLe1 hinvQ
  have h2le : eta ^ ((2 : ℝ)⁻¹) ≤ eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) :=
    Real.rpow_le_rpow_of_exponent_ge heta0 hetaLe1 hinv2
  have hqQ0 : (0 : ℝ) < eta ^ ((initExpQ d g : ℝ)⁻¹) := Real.rpow_pos_of_pos heta0 _
  have hU0 : 0 ≤ UStar := by
    rw [hUstar]; positivity
  have hUle : UStar ≤ Sfull * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) := by
    rw [hUstar, ← hSsum]
    have h1 : (Scen + Scell) * eta ^ ((initExpQ d g : ℝ)⁻¹) ≤
        (Scen + Scell) * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left hqle (by linarith only [hScen0, hScell0])
    linarith only [h1]
  have hB0 : 0 ≤ BStar := by rw [hBstar]; positivity
  have hBle : BStar ≤ (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) *
      eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) := by
    rw [hBstar]
    exact mul_le_mul_of_nonneg_left h2le (Real.rpow_nonneg (by norm_num) _)
  have hrow0 : (0 : ℝ) < (3 : ℝ) ^ (-initExpA g * (H : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h3aH : (3 : ℝ) ^ (-initExpA g * (H : ℝ)) = ((3 : ℝ) ^ (-initExpA g)) ^ H := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  -- the three coefficients of `𝓡_*` are below the uniform majorant `W`
  have hcoef1 : Cd * KStar * LenStar ≤ W := by
    have e1 : Cd * KStar ≤ Cd * (2 * ((2 : ℝ) ^ d) ^ 2) :=
      mul_le_mul_of_nonneg_left hK2 hCd0.le
    have e2 : Cd * KStar * LenStar ≤ Cd * (2 * ((2 : ℝ) ^ d) ^ 2) * (4 * (2 : ℝ) ^ d) :=
      mul_le_mul e1 hLen2 (by linarith only [hLen1]) (by positivity)
    have e3 : Cd * (2 * ((2 : ℝ) ^ d) ^ 2) * (4 * (2 : ℝ) ^ d) =
        8 * Cd * ((2 : ℝ) ^ d) ^ 3 := by ring
    linarith only [e2, e3, hW1]
  have hcoef3 : cconst * KStar * LenStar ≤ W := by
    have e1 : cconst * KStar ≤ 3 * (2 * ((2 : ℝ) ^ d) ^ 2) :=
      mul_le_mul hcc3 hK2 (by linarith only [hK1]) (by norm_num)
    have e2 : cconst * KStar * LenStar ≤ 3 * (2 * ((2 : ℝ) ^ d) ^ 2) * (4 * (2 : ℝ) ^ d) :=
      mul_le_mul e1 hLen2 (by linarith only [hLen1]) (by positivity)
    have e3 : (3 : ℝ) * (2 * ((2 : ℝ) ^ d) ^ 2) * (4 * (2 : ℝ) ^ d) =
        24 * ((2 : ℝ) ^ d) ^ 3 := by ring
    linarith only [e2, e3, hW2]
  have hnum : Cd * KStar * Real.sqrt 2 * LambdaStar ≤ 24 * Cd * ((2 : ℝ) ^ d) ^ 3 := by
    have hs2 : Real.sqrt 2 ≤ 2 := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have e1 : Cd * KStar ≤ Cd * (2 * ((2 : ℝ) ^ d) ^ 2) :=
      mul_le_mul_of_nonneg_left hK2 hCd0.le
    have e2 : Cd * KStar * Real.sqrt 2 ≤ Cd * (2 * ((2 : ℝ) ^ d) ^ 2) * 2 :=
      mul_le_mul e1 hs2 (Real.sqrt_nonneg 2) (by positivity)
    have e3 : Cd * KStar * Real.sqrt 2 * LambdaStar ≤
        Cd * (2 * ((2 : ℝ) ^ d) ^ 2) * 2 * (6 * (2 : ℝ) ^ d) :=
      mul_le_mul e2 hLam2 hLam1 (by positivity)
    have e4 : Cd * (2 * ((2 : ℝ) ^ d) ^ 2) * 2 * (6 * (2 : ℝ) ^ d) =
        24 * Cd * ((2 : ℝ) ^ d) ^ 3 := by ring
    linarith only [e3, e4]
  have hcoef2 : Cd * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) ≤ W := by
    rw [div_le_iff₀ (by linarith only [ha] : (0 : ℝ) < 2 * initExpA g)]
    linarith only [hnum, hW3]
  have hcoef2nn : (0 : ℝ) ≤ Cd * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) :=
    div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hCd0.le (by linarith only [hK1]))
        (Real.sqrt_nonneg 2)) hLam1) (by linarith only [ha])
  have hR0 : 0 ≤ RStar := by
    rw [hRstar]
    have p1 : (0 : ℝ) ≤ Cd * KStar * LenStar * UStar :=
      mul_nonneg (mul_nonneg (mul_nonneg hCd0.le (by linarith only [hK1]))
        (by linarith only [hLen1])) hU0
    have p2 : (0 : ℝ) ≤ Cd * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
        (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) :=
      mul_nonneg hcoef2nn (by linarith only [hB0, hrow0])
    have p3 : (0 : ℝ) ≤ cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hcc1])
        (by linarith only [hK1])) (by linarith only [hLen1])) hqQ0.le
    linarith only [p1, p2, p3]
  refine ⟨hR0, ?_⟩
  have hRle : RStar ≤ Real.sqrt s := by
    have p1 : Cd * KStar * LenStar * UStar ≤
        W * (Sfull * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹)) := by
      have e1 : Cd * KStar * LenStar * UStar ≤ W * UStar :=
        mul_le_mul_of_nonneg_right hcoef1 hU0
      have e2 : W * UStar ≤ W * (Sfull * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹)) :=
        mul_le_mul_of_nonneg_left hUle hW0
      linarith only [e1, e2]
    have p2 : Cd * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
          (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) ≤
        W * ((2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) *
          eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) := by
      have e1 : Cd * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
          (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) ≤
          W * (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoef2 (by linarith only [hB0, hrow0])
      have e2 : W * (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) ≤
          W * ((2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) *
            eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) +
              (3 : ℝ) ^ (-initExpA g * (H : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith only [hBle]) hW0
      linarith only [e1, e2]
    have p3 : cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹) ≤
        W * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) := by
      have e1 : cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹) ≤
          W * eta ^ ((initExpQ d g : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hcoef3 hqQ0.le
      have e2 : W * eta ^ ((initExpQ d g : ℝ)⁻¹) ≤
          W * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hqle hW0
      linarith only [e1, e2]
    have hrowle : W * (3 : ℝ) ^ (-initExpA g * (H : ℝ)) ≤ Real.sqrt s / 2 := by
      rw [h3aH]; exact hHrow
    have hcollapse : W * (Sfull * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹)) +
        W * ((2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) *
          eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) +
        W * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) =
      W * (Sfull + (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) + 1) *
          eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) +
        W * (3 : ℝ) ^ (-initExpA g * (H : ℝ)) := by ring
    rw [hRstar]
    linarith only [p1, p2, p3, hcollapse, hetakey, hrowle]
  nlinarith only [hR0, hRle, Real.sq_sqrt hs.le]

/-- **The coefficient below the budget**: with the determinant slack past its
threshold, the lower-edge factor past its own and the weak constant already
below `√s`, each of the five summands of `ω_rsp` is at most `s`, so
`ω_rsp ≤ 10C_ds`.  This is the `δ_det ↓ 0` and `H ↑ ∞` half of the choice of the
finite-window summation coefficients. -/
theorem omega_le_of_slack {d : ℕ} {Cd deltaDet tau0 s TStar AStar LStar RStar
    omegaRsp : ℝ} {H : ℕ} (hCd : 1 ≤ Cd) (hs : 0 < s) (htau0 : 0 < tau0)
    (htauS : tau0 ≤ s) (htauQ : 1024 * ((2 : ℝ) ^ d) ^ 3 * tau0 ≤ s ^ 2)
    (hT1 : 0 ≤ TStar) (hT2 : TStar ≤ 4 * ((2 : ℝ) ^ d) ^ 2 * deltaDet)
    (hdeltaT : 4 * ((2 : ℝ) ^ d) ^ 2 * deltaDet ≤ tau0)
    (hA1 : 2 ≤ AStar) (hA2 : AStar ≤ 4 * (2 : ℝ) ^ d)
    (hL1 : 0 ≤ LStar) (hL2 : LStar ≤ 1024 * ((2 : ℝ) ^ d) ^ 3)
    (hHedge : 68 * ((2 : ℝ) ^ d) ^ 2 * ((1 : ℝ) / 3) ^ H ≤ s) (hR2 : RStar ^ 2 ≤ s)
    (homega : omegaRsp = 2 * Cd * (TStar + Real.sqrt (TStar * AStar) +
      Real.sqrt (TStar * LStar) +
      (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar)) + RStar ^ 2)) :
    0 ≤ omegaRsp ∧ omegaRsp ≤ 10 * Cd * s := by
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hM0 : (0 : ℝ) ≤ (2 : ℝ) ^ d := le_trans zero_le_one hM1
  have hTs : TStar ≤ tau0 := le_trans hT2 hdeltaT
  have hterm1 : TStar ≤ s := le_trans hTs htauS
  have hTA : TStar * AStar ≤ s ^ 2 := by
    have h1 : TStar * AStar ≤ tau0 * (4 * (2 : ℝ) ^ d) :=
      mul_le_mul hTs hA2 (by linarith only [hA1]) (le_of_lt htau0)
    have hMt : (0 : ℝ) ≤ (2 : ℝ) ^ d * tau0 := mul_nonneg hM0 htau0.le
    have hMsq : (1 : ℝ) ≤ ((2 : ℝ) ^ d) ^ 2 := one_le_pow₀ hM1
    have hstep : (2 : ℝ) ^ d * tau0 ≤ ((2 : ℝ) ^ d) ^ 3 * tau0 := by
      nlinarith only [hMt, hMsq]
    linarith only [h1, hstep, hMt, htauQ]
  have hTL : TStar * LStar ≤ s ^ 2 := by
    have h1 : TStar * LStar ≤ tau0 * (1024 * ((2 : ℝ) ^ d) ^ 3) :=
      mul_le_mul hTs hL2 hL1 (le_of_lt htau0)
    nlinarith only [h1, htauQ]
  have hterm2 : Real.sqrt (TStar * AStar) ≤ s := sqrt_le_of_sq_le hs.le hTA
  have hterm3 : Real.sqrt (TStar * LStar) ≤ s := sqrt_le_of_sq_le hs.le hTL
  have hAL : Real.sqrt (AStar * LStar) ≤ 64 * ((2 : ℝ) ^ d) ^ 2 := by
    refine sqrt_le_of_sq_le (by positivity) ?_
    have h1 : AStar * LStar ≤ 4 * (2 : ℝ) ^ d * (1024 * ((2 : ℝ) ^ d) ^ 3) :=
      mul_le_mul hA2 hL2 hL1 (by linarith only [hM0])
    nlinarith only [h1]
  have h3H : (3 : ℝ) ^ (-(H : ℝ)) = ((1 : ℝ) / 3) ^ H := by
    rw [show (-(H : ℝ)) = (-1 : ℝ) * (H : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
    norm_num
  have hterm4 : (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar)) ≤ s := by
    have hsum : AStar + Real.sqrt (AStar * LStar) ≤ 68 * ((2 : ℝ) ^ d) ^ 2 := by
      nlinarith only [hA2, hAL, hM1]
    have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
    calc (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar))
        ≤ (3 : ℝ) ^ (-(H : ℝ)) * (68 * ((2 : ℝ) ^ d) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum hpow
      _ = 68 * ((2 : ℝ) ^ d) ^ 2 * ((1 : ℝ) / 3) ^ H := by rw [h3H]; ring
      _ ≤ s := hHedge
  refine ⟨omegaRsp_nonneg hCd0.le hT1 (by linarith only [hA1])
    (Real.rpow_nonneg (by norm_num) _) homega, ?_⟩
  rw [homega]
  nlinarith only [hCd0, hterm1, hterm2, hterm3, hterm4, hR2]

/-! ## The closing contradiction -/

/-- **The fixed-window absorption** at the canonical comparisons of the two
response endpoints.  If `κ_t - 1 > δ_ad` then
`κ_t ≤ (1+δ_ad^{-1})(κ_t-1)`, and the canonical comparison, the normalized
response and the factor-`12d` estimate chain into
`κ_t - 1 ≤ 12dω_rsp R^{2d}(1+δ_ad^{-1})(κ_t-1)`, contradicting the numerical
absorption closing the response estimate. -/
theorem imbalance_le_of_absorption {d : ℕ} {kappaT kappaS omegaRsp Rpow deltaAd resp : ℝ}
    (hAd : 0 < deltaAd)
    (habs : 12 * (d : ℝ) * omegaRsp * Rpow * (1 + deltaAd⁻¹) < 1)
    (homega : 0 ≤ omegaRsp) (hRpow : 0 ≤ Rpow)
    (hfactor : kappaT - 1 ≤ 12 * (d : ℝ) * resp)
    (hresp : resp ≤ omegaRsp * kappaS)
    (hcomp : kappaS ≤ Rpow * kappaT) :
    kappaT ≤ 1 + deltaAd := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < kappaT - 1 := by linarith only [hcon, hAd]
  have hd0 : (0 : ℝ) ≤ 12 * (d : ℝ) := by positivity
  have hX0 : (0 : ℝ) ≤ 12 * (d : ℝ) * omegaRsp * Rpow := by positivity
  have hstep1 : kappaT - 1 ≤ 12 * (d : ℝ) * omegaRsp * kappaS := by
    have h := mul_le_mul_of_nonneg_left hresp hd0
    linarith only [hfactor, h]
  have hstep2 : 12 * (d : ℝ) * omegaRsp * kappaS ≤
      12 * (d : ℝ) * omegaRsp * Rpow * kappaT := by
    have h := mul_le_mul_of_nonneg_left hcomp
      (by positivity : (0 : ℝ) ≤ 12 * (d : ℝ) * omegaRsp)
    linarith only [h]
  have hinv : 1 ≤ (kappaT - 1) * deltaAd⁻¹ := by
    have h := mul_le_mul_of_nonneg_right (le_of_lt (by linarith only [hcon] :
      deltaAd < kappaT - 1)) (le_of_lt (inv_pos.mpr hAd))
    rwa [mul_inv_cancel₀ (ne_of_gt hAd)] at h
  have hrearrange : kappaT ≤ (1 + deltaAd⁻¹) * (kappaT - 1) := by
    have hexp : (1 + deltaAd⁻¹) * (kappaT - 1) =
        (kappaT - 1) + (kappaT - 1) * deltaAd⁻¹ := by ring
    linarith only [hexp, hinv]
  have hstep3 : 12 * (d : ℝ) * omegaRsp * Rpow * kappaT ≤
      12 * (d : ℝ) * omegaRsp * Rpow * ((1 + deltaAd⁻¹) * (kappaT - 1)) :=
    mul_le_mul_of_nonneg_left hrearrange hX0
  have hstep4 : 12 * (d : ℝ) * omegaRsp * Rpow * ((1 + deltaAd⁻¹) * (kappaT - 1)) <
      kappaT - 1 := by
    nlinarith only [habs, hpos]
  linarith only [hstep1, hstep2, hstep3, hstep4]

/-- The same closing contradiction with the determinant factor in its printed
form `R^{2d} = (1+δ_det)^{2d}`. -/
theorem imbalance_le_of_absorption_rpow {d : ℕ}
    {kappaT kappaS omegaRsp deltaDet deltaAd resp : ℝ} (hAd : 0 < deltaAd)
    (hDet : 0 ≤ deltaDet)
    (habs : 12 * (d : ℝ) * omegaRsp * (1 + deltaDet) ^ (2 * (d : ℝ)) *
      (1 + deltaAd⁻¹) < 1)
    (homega : 0 ≤ omegaRsp)
    (hfactor : kappaT - 1 ≤ 12 * (d : ℝ) * resp)
    (hresp : resp ≤ omegaRsp * kappaS)
    (hcomp : kappaS ≤ (1 + deltaDet) ^ (2 * (d : ℝ)) * kappaT) :
    kappaT ≤ 1 + deltaAd :=
  imbalance_le_of_absorption hAd habs homega
    (Real.rpow_nonneg (by linarith only [hDet]) _) hfactor hresp hcomp

end

end Response
end HighContrast
end Homogenization
