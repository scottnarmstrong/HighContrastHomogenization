/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.Boundary
import HCPoly.Provider.Response.Exponents
import HCPoly.Provider.Transport.WindowMomentBound

/-!
# The lower-scale buffer of the response window

The response window is closed from below by a buffer `B_resp` chosen after the
downstream caps and the witness-radius exponent `A_rad`, and before the
coefficient law and its aspect ratio.  It is asked to satisfy the slack in the
source exponent and the two smallness bounds, for the terminal source
contribution and for the source row, at the source constant `C_buf = C_d ζ_g`.
Since `ρ_max > 0` and `3/2 > 0`, both exponents
`1 + 2A_rad - ρ_max B_resp` and `1 + 2A_rad - (3/2)B_resp` tend to `-∞` with
`B_resp`, so such a buffer exists; this is `exists_bresp`.

The buffer is used through the scale hypothesis
`j_* + ⌈B_resp log₃(2+Π)⌉ ≤ s` of `e.global.selection.scales`, which converts a
base-three decay into a decay in the aspect ratio at the buffered rate.  With the
reference-ratio bound and the eccentricity bound `e.global.selection.eccentricity`,
and with the same-window multiplier moments, that gives the two source
allocations: the smallness of the below-start source maximum and the smallness of
the all-earlier source row.  The factor `24` of both is
`6 · 4`: the reference ratio contributes `κ_𝐄 ≤ 6Π` and the multiplier moments
contribute `E[Y_P]‖Y_P‖_{L^Q} ≤ 4`, respectively `(E[Y_P])² ≤ 4`.
-/

namespace Homogenization
namespace HighContrast
namespace Response

open MeasureTheory

noncomputable section

/-! ## Scalar tails -/

/-- The row denominator `3^{3/2-g} - 1` of the source-row smallness bound is
positive below the source exponent one. -/
theorem one_lt_three_rpow_row {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    1 < (3 : ℝ) ^ (3 / 2 - g) := by
  have hpos : (0 : ℝ) < 3 / 2 - g := by linarith only [hg.2]
  have h := Real.rpow_lt_rpow_of_exponent_lt (x := (3 : ℝ)) (by norm_num) hpos
  rwa [Real.rpow_zero] at h

/-- A positive multiple of a base-three power whose exponent decreases at a
positive rate is eventually below any positive threshold. -/
theorem exists_forall_le_of_rpow_three {c r rho x : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hrho : 0 < rho) :
    ∃ B0 : ℝ, ∀ B : ℝ, B0 ≤ B → c * (3 : ℝ) ^ (x - rho * B) ≤ r := by
  refine ⟨(x - Real.logb 3 (r / c)) / rho, fun B hB => ?_⟩
  have hrc : 0 < r / c := div_pos hr hc
  have hB' := (div_le_iff₀ hrho).mp hB
  have hle : x - rho * B ≤ Real.logb 3 (r / c) := by linarith only [hB']
  calc c * (3 : ℝ) ^ (x - rho * B)
      ≤ c * (3 : ℝ) ^ Real.logb 3 (r / c) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle) hc.le
    _ = c * (r / c) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hrc]
    _ = r := by field_simp

/-- **The source buffer** meeting the slack in the source exponent, the
smallness of the terminal source contribution, and the smallness of the source
row: after the downstream caps and the witness-radius exponent are fixed, a
lower-scale buffer beyond all three thresholds exists.  No coefficient law and no
aspect ratio enters. -/
theorem exists_bresp {d : ℕ} (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {Cd : ℝ} (hCd : 1 ≤ Cd) {eta : ℝ} (heta : 0 < eta) (Arad : ℝ) :
    ∃ Bresp : ℝ, 0 < Bresp ∧
      1 + 2 * Arad < initExpRhoMax d g * Bresp ∧
      24 * (Cd * zetaG g) ^ 2 *
          (3 : ℝ) ^ (1 + 2 * Arad - initExpRhoMax d g * Bresp) ≤
        1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹) ∧
      24 * (Cd * zetaG g) ^ 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
          (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ 1 := by
  have hrho : 0 < initExpRhoMax d g := zero_lt_initExpRhoMax hd hg
  have hCz : (0 : ℝ) < Cd * zetaG g :=
    mul_pos (lt_of_lt_of_le zero_lt_one hCd)
      (lt_of_lt_of_le zero_lt_one (Initialization.one_le_zetaG hg))
  have hc : (0 : ℝ) < 24 * (Cd * zetaG g) ^ 2 := by
    have h := pow_pos hCz 2
    linarith only [h]
  have hD : (0 : ℝ) < (3 : ℝ) ^ (3 / 2 - g) - 1 := by
    have h := one_lt_three_rpow_row hg
    linarith only [h]
  have hetapow : (0 : ℝ) < eta ^ ((initExpQ d g : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos heta _
  have hr : (0 : ℝ) < 1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹) := by
    linarith only [hetapow]
  obtain ⟨B1, hB1⟩ :=
    exists_forall_le_of_rpow_three (c := 24 * (Cd * zetaG g) ^ 2)
      (r := 1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹))
      (rho := initExpRhoMax d g) (x := 1 + 2 * Arad) hc hr hrho
  obtain ⟨B2, hB2⟩ :=
    exists_forall_le_of_rpow_three
      (c := 24 * (Cd * zetaG g) ^ 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1)) (r := 1)
      (rho := 3 / 2) (x := 1 + 2 * Arad) (div_pos hc hD) zero_lt_one (by norm_num)
  refine ⟨max (max B1 B2) (max ((2 + 2 * Arad) / initExpRhoMax d g) 1), ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right _ (1 : ℝ)) (le_max_right _ _))
  · have hge : (2 + 2 * Arad) / initExpRhoMax d g ≤
        max (max B1 B2) (max ((2 + 2 * Arad) / initExpRhoMax d g) 1) :=
      le_trans (le_max_left _ (1 : ℝ)) (le_max_right _ _)
    have h := (div_le_iff₀ hrho).mp hge
    linarith only [h]
  · exact hB1 _ (le_trans (le_max_left B1 B2) (le_max_left _ _))
  · exact hB2 _ (le_trans (le_max_right B1 B2) (le_max_left _ _))

/-! ## The source allocation of the response window -/

/-- The mean of the common window multiplier is at most two, so the same-window
moment bounds for the source multiplier give `E[Y_P]‖Y_P‖_{L^Q} ≤ 4` and
`(E[Y_P])² ≤ 4`. -/
theorem integral_le_two {d : ℕ} {P : Measure (CoeffSpace d)} {Q : ℝ}
    {Y : CoeffSpace d → ℝ}
    (hnorm : ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y)
    (htwo : lqNorm P Q Y ≤ 2) :
    (∫ a, Y a ∂P) ≤ 2 := Transport.integral_le_two hnorm htwo

/-- A nonpositive power of `2 + Π` is bounded by the same power of three, the
aspect ratio being at least one. -/
theorem rpow_aspect_le_rpow_three {Pi x : ℝ} (hPi : 1 ≤ Pi) (hx : x ≤ 0) :
    (2 + Pi) ^ x ≤ (3 : ℝ) ^ x :=
  Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith only [hPi]) hx

/-- The scale hypothesis of `e.global.selection.eccentricity`
converts a base-three decay at a positive rate into a decay in `2 + Π` at the
buffered rate. -/
theorem rpow_three_le_rpow_aspect {c Pi Bresp : ℝ} {jStar k : ℤ} (hc : 0 < c)
    (hPi : 1 ≤ Pi)
    (hbuf : jStar + ⌈Bresp * Real.logb 3 (2 + Pi)⌉ ≤ k) :
    (3 : ℝ) ^ (-c * ((k : ℝ) - (jStar : ℝ))) ≤ (2 + Pi) ^ (-(c * Bresp)) := by
  have hPi0 : (0 : ℝ) < 2 + Pi := by linarith only [hPi]
  have hceil : (⌈Bresp * Real.logb 3 (2 + Pi)⌉ : ℝ) ≤ (k : ℝ) - (jStar : ℝ) := by
    have hcast : ((jStar + ⌈Bresp * Real.logb 3 (2 + Pi)⌉ : ℤ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hbuf
    push_cast at hcast
    linarith only [hcast]
  have hL : Bresp * Real.logb 3 (2 + Pi) ≤ (k : ℝ) - (jStar : ℝ) :=
    le_trans (Int.le_ceil _) hceil
  have hmul := mul_le_mul_of_nonneg_left hL hc.le
  have hkey : (3 : ℝ) ^ (Real.logb 3 (2 + Pi) * (-(c * Bresp)))
      = (2 + Pi) ^ (-(c * Bresp)) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) hPi0]
  calc (3 : ℝ) ^ (-c * ((k : ℝ) - (jStar : ℝ)))
      ≤ (3 : ℝ) ^ (Real.logb 3 (2 + Pi) * (-(c * Bresp))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hmul])
    _ = (2 + Pi) ^ (-(c * Bresp)) := hkey

/-- The reference ratio and the witness eccentricity of the buffer display
bound the block factor of the source allocation by `6C_buf²(2+Π)^{1+2A_rad}`. -/
theorem block_factor_le {d : ℕ} {Cd g : ℝ} {E : BlockMat d} {m0 : Mat d}
    {Arad : ℝ} (hPi : 1 ≤ aspectRatio E)
    (hkap : kappaRef E ≤ 6 * aspectRatio E)
    (hecc : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad) :
    kappaRef E * boundaryConst Cd g m0 ^ 2 ≤
      6 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) := by
  have hPi0 : (0 : ℝ) < 2 + aspectRatio E := by linarith only [hPi]
  have hecc0 : 0 ≤ witnessEccentricity m0 := by
    rw [witnessEccentricity]
    exact Real.sqrt_nonneg _
  have hepow : 0 ≤ (2 + aspectRatio E) ^ Arad := Real.rpow_nonneg hPi0.le _
  have hsq : (2 + aspectRatio E) ^ (2 * Arad)
      = (2 + aspectRatio E) ^ Arad * (2 + aspectRatio E) ^ Arad := by
    rw [two_mul, Real.rpow_add hPi0]
  have hsqle : witnessEccentricity m0 ^ 2 ≤ (2 + aspectRatio E) ^ (2 * Arad) := by
    rw [hsq, pow_two]
    exact mul_le_mul hecc hecc hecc0 hepow
  have hexpand : boundaryConst Cd g m0 ^ 2
      = (Cd * zetaG g) ^ 2 * witnessEccentricity m0 ^ 2 := by
    rw [boundaryConst]
    ring
  have hbsq : boundaryConst Cd g m0 ^ 2 ≤
      (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (2 * Arad) := by
    rw [hexpand]
    exact mul_le_mul_of_nonneg_left hsqle (sq_nonneg _)
  have hnn : 0 ≤ (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (2 * Arad) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hPi0.le _)
  calc kappaRef E * boundaryConst Cd g m0 ^ 2
      ≤ 6 * aspectRatio E * boundaryConst Cd g m0 ^ 2 :=
        mul_le_mul_of_nonneg_right hkap (sq_nonneg _)
    _ ≤ 6 * aspectRatio E *
          ((Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (2 * Arad)) :=
        mul_le_mul_of_nonneg_left hbsq (by linarith only [hPi])
    _ ≤ 6 * (2 + aspectRatio E) *
          ((Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (2 * Arad)) :=
        mul_le_mul_of_nonneg_right (by linarith only []) hnn
    _ = 6 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) := by
        rw [Real.rpow_add hPi0, Real.rpow_one]
        ring

/-- **The source maximum bound**, the smallness of the below-start source
maximum: the majorant of that source moment is below the terminal smallness
threshold at every scale beyond the start. -/
theorem source_maximum_bound {d : ℕ} (hd : 2 ≤ d) {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {Cd : ℝ} {E : BlockMat d} {m0 : Mat d}
    {eta Arad Bresp : ℝ} {jStar s t : ℤ} (hPi : 1 ≤ aspectRatio E)
    (hslack : 1 + 2 * Arad < initExpRhoMax d g * Bresp)
    (hterm : 24 * (Cd * zetaG g) ^ 2 *
        (3 : ℝ) ^ (1 + 2 * Arad - initExpRhoMax d g * Bresp) ≤
      1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹))
    (hkap : kappaRef E ≤ 6 * aspectRatio E)
    (hecc : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hbuf : jStar + ⌈Bresp * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s)
    (hst : s < t) :
    4 * kappaRef E * boundaryConst Cd g m0 ^ 2 *
        (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jStar : ℝ))) ≤
      1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹) := by
  have hrho : 0 < initExpRhoMax d g := zero_lt_initExpRhoMax hd hg
  have hPi0 : (0 : ℝ) < 2 + aspectRatio E := by linarith only [hPi]
  have hfac : 4 * kappaRef E * boundaryConst Cd g m0 ^ 2 ≤
      24 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) := by
    have h := mul_le_mul_of_nonneg_left
      (block_factor_le (Cd := Cd) (g := g) hPi hkap hecc)
      (by norm_num : (0 : ℝ) ≤ 4)
    calc 4 * kappaRef E * boundaryConst Cd g m0 ^ 2
        = 4 * (kappaRef E * boundaryConst Cd g m0 ^ 2) := by ring
      _ ≤ 4 * (6 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad)) := h
      _ = 24 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) := by ring
  have hdecay : (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jStar : ℝ))) ≤
      (2 + aspectRatio E) ^ (-(initExpRhoMax d g * Bresp)) :=
    rpow_three_le_rpow_aspect hrho hPi (le_trans hbuf (le_of_lt hst))
  have hX : (0 : ℝ) < (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jStar : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hb0 : (0 : ℝ) ≤ 24 * (Cd * zetaG g) ^ 2 *
      (2 + aspectRatio E) ^ (1 + 2 * Arad) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg hPi0.le _)
  have hcollapse : (2 + aspectRatio E) ^ (1 + 2 * Arad) *
        (2 + aspectRatio E) ^ (-(initExpRhoMax d g * Bresp)) =
      (2 + aspectRatio E) ^ (1 + 2 * Arad - initExpRhoMax d g * Bresp) := by
    rw [← Real.rpow_add hPi0, sub_eq_add_neg]
  have hneg : 1 + 2 * Arad - initExpRhoMax d g * Bresp ≤ 0 := by
    linarith only [hslack]
  have hc0 : (0 : ℝ) ≤ 24 * (Cd * zetaG g) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  calc 4 * kappaRef E * boundaryConst Cd g m0 ^ 2 *
        (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jStar : ℝ)))
      ≤ 24 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) *
          (2 + aspectRatio E) ^ (-(initExpRhoMax d g * Bresp)) :=
        mul_le_mul hfac hdecay hX.le hb0
    _ = 24 * (Cd * zetaG g) ^ 2 *
          (2 + aspectRatio E) ^ (1 + 2 * Arad - initExpRhoMax d g * Bresp) := by
        rw [mul_assoc, hcollapse]
    _ ≤ 24 * (Cd * zetaG g) ^ 2 *
          (3 : ℝ) ^ (1 + 2 * Arad - initExpRhoMax d g * Bresp) :=
        mul_le_mul_of_nonneg_left (rpow_aspect_le_rpow_three hPi hneg) hc0
    _ ≤ 1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹) := hterm

/-- **The all-earlier row bound**, the smallness of the all-earlier source row:
the same multiplier read at the start scale, with the row exponent negative
because `ρ_max < 3/2`. -/
theorem source_row_bound {d : ℕ} (hd : 2 ≤ d) {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {Cd : ℝ} {E : BlockMat d} {m0 : Mat d}
    {EY Arad Bresp : ℝ} {jStar s : ℤ} (hPi : 1 ≤ aspectRatio E)
    (hBresp : 0 < Bresp)
    (hslack : 1 + 2 * Arad < initExpRhoMax d g * Bresp)
    (hrow : 24 * (Cd * zetaG g) ^ 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ 1)
    (hkap : kappaRef E ≤ 6 * aspectRatio E)
    (hecc : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hEY0 : 0 ≤ EY) (hEY : EY ≤ 2)
    (hbuf : jStar + ⌈Bresp * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s) :
    kappaRef E * boundaryConst Cd g m0 ^ 2 * EY ^ 2 /
          ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) ≤ 1 := by
  have hPi0 : (0 : ℝ) < 2 + aspectRatio E := by linarith only [hPi]
  have hD : (0 : ℝ) < (3 : ℝ) ^ (3 / 2 - g) - 1 := by
    have h := one_lt_three_rpow_row hg
    linarith only [h]
  have hrow' : 24 * (Cd * zetaG g) ^ 2 *
      (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ (3 : ℝ) ^ (3 / 2 - g) - 1 := by
    rwa [div_mul_eq_mul_div, div_le_one hD] at hrow
  have hEY2 : EY ^ 2 ≤ 4 := by
    have h := mul_self_le_mul_self hEY0 hEY
    rw [pow_two]
    linarith only [h]
  have h6 : (0 : ℝ) ≤ 6 * (Cd * zetaG g) ^ 2 *
      (2 + aspectRatio E) ^ (1 + 2 * Arad) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg hPi0.le _)
  have hfac : kappaRef E * boundaryConst Cd g m0 ^ 2 * EY ^ 2 ≤
      24 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) := by
    have h := mul_le_mul (block_factor_le hPi hkap hecc) hEY2 (sq_nonneg EY) h6
    calc kappaRef E * boundaryConst Cd g m0 ^ 2 * EY ^ 2
        ≤ 6 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) * 4 := h
      _ = 24 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) := by ring
  have hdecay : (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) ≤
      (2 + aspectRatio E) ^ (-(3 / 2 * Bresp)) :=
    rpow_three_le_rpow_aspect (by norm_num) hPi hbuf
  have hX : (0 : ℝ) < (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hb0 : (0 : ℝ) ≤ 24 * (Cd * zetaG g) ^ 2 *
      (2 + aspectRatio E) ^ (1 + 2 * Arad) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg hPi0.le _)
  have hcollapse : (2 + aspectRatio E) ^ (1 + 2 * Arad) *
        (2 + aspectRatio E) ^ (-(3 / 2 * Bresp)) =
      (2 + aspectRatio E) ^ (1 + 2 * Arad - 3 / 2 * Bresp) := by
    rw [← Real.rpow_add hPi0, sub_eq_add_neg]
  have hneg : 1 + 2 * Arad - 3 / 2 * Bresp ≤ 0 := by
    have h := mul_lt_mul_of_pos_right (initExpRhoMax_lt_three_halves hd hg) hBresp
    linarith only [h, hslack]
  have hc0 : (0 : ℝ) ≤ 24 * (Cd * zetaG g) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  rw [div_mul_eq_mul_div, div_le_one hD]
  calc kappaRef E * boundaryConst Cd g m0 ^ 2 * EY ^ 2 *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ)))
      ≤ 24 * (Cd * zetaG g) ^ 2 * (2 + aspectRatio E) ^ (1 + 2 * Arad) *
          (2 + aspectRatio E) ^ (-(3 / 2 * Bresp)) :=
        mul_le_mul hfac hdecay hX.le hb0
    _ = 24 * (Cd * zetaG g) ^ 2 *
          (2 + aspectRatio E) ^ (1 + 2 * Arad - 3 / 2 * Bresp) := by
        rw [mul_assoc, hcollapse]
    _ ≤ 24 * (Cd * zetaG g) ^ 2 *
          (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) :=
        mul_le_mul_of_nonneg_left (rpow_aspect_le_rpow_three hPi hneg) hc0
    _ ≤ (3 : ℝ) ^ (3 / 2 - g) - 1 := hrow'

end

end Response
end HighContrast
end Homogenization
