/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Persistence.TransferGauge

/-!
# The deterministic transfer cost

The forward and the reverse decay gap of `e.response.transfer.gaps` are ceilings
of truncated logarithms of the deterministic comparison size, read at two
different scales and against two different tolerances.  This file pays for both
at once.

Everything rests on one envelope.  Under the radius bound
`e.global.selection.eccentricity` the witness eccentricity is at most
`(2 + Π)^{A_rad}`, and the deterministic size carries its square; the terminal
normalization `e.two.grid.source.normalization` bounds
the reference ratio by `6 Π`; and above the alignment the gauge bound of
`e.source.lower.scale` puts the source gauge below
`2^g/(1-g)`.  Together these give the uniform envelope for the transfer size: at
every scale at or above the alignment the deterministic size is below one fixed
multiple of `Π(2+Π)^{2A_rad}`.

The gap arithmetic is then elementary.  A ceiling of `max{1, x⁺}` never exceeds
`x⁺ + 2`; and the truncated logarithm is monotone through the degenerate branch
as well, since the truncation returns zero exactly where the logarithm is at its
junk value.  Applying both to the two gaps and using `η_min ≤ η_+, η_-` gives
the exact two-gap cost.

The logarithmic form of that cost is the exact form with the aspect ratio
divided out.  Splitting the logarithm of the
envelope as `log_3 K_0 + log_3 Π + 2A_rad log_3(2 + Π)` and using
`log_3 Π ≤ log_3(2 + Π)` leaves a bound of the shape `C_0 + 2(1 + 2A_rad)L` with
`L = log_3(2 + Π) ≥ 1`, which is below `(C_0 + 2(1 + 2A_rad))L`.  The constant
`C_0 + 2(1 + 2A_rad)` mentions the reference block nowhere, which is why the
entry argument may fix it before the law.

There are no definitions in this file.
-/

namespace Homogenization
namespace HighContrast
namespace Persistence

noncomputable section

variable {d : ℕ}

/-! ## The two elementary estimates -/

/-- **The ceiling estimate** of `e.response.transfer.gaps`: a gap, being the
ceiling of `max{1, x⁺}`, never exceeds `x⁺ + 2`. -/
theorem gapCeil_le_add_two (x : ℝ) :
    ((⌈max 1 (max 0 x)⌉ : ℤ) : ℝ) ≤ max 0 x + 2 := by
  have h : max 1 (max 0 x) ≤ max 0 x + 1 := by
    refine max_le ?_ (by linarith only)
    have h0 : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    linarith only [h0]
  have hceil := Int.ceil_le_ceil h
  refine le_trans (Int.cast_le.mpr hceil) ?_
  have hlt := Int.ceil_lt_add_one (max 0 x + 1)
  linarith only [hlt]

/-- **The truncated logarithm is monotone**, including through the degenerate
branch: where the argument vanishes the logarithm is at its junk value zero,
which the truncation returns anyway. -/
theorem max_logb_le_max_logb {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    max 0 (Real.logb 3 x) ≤ max 0 (Real.logb 3 y) := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.logb_zero, max_self]
    exact le_max_left _ _
  · exact max_le_max le_rfl
      (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3) h hxy)

/-! ## The common cost envelope -/

/-- The deterministic comparison size is nonnegative: every factor is, the
reference ratio because it is an infimum of nonnegative numbers and the source
gauge because its base exceeds one. -/
theorem zero_le_transferSizeBar {U CAE Cd g K : ℝ} {E : BlockMat d} {m0 : Mat d}
    {j : ℤ} (hU : 0 ≤ U) (hCAE : 0 ≤ CAE) (hCd : 0 ≤ Cd) (hg1 : g < 1) :
    0 ≤ transferSizeBar U CAE Cd g K E m0 j := by
  rw [transferSizeBar]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg hU hCAE) hCd) (Transport.zero_le_kappaRef E)) (sq_nonneg _))
    (Transport.zero_lt_zetaG hg1).le) (zero_lt_transferGauge hg1 K j).le

/-- **The common cost envelope** for the transfer size.  The reference ratio is
below `6 Π` by the terminal normalization, the squared witness eccentricity
is below `(2 + Π)^{2A_rad}` by the radius bound, and the source gauge is below
`2^g/(1-g)` above the alignment; the remaining factors are the same on both
sides. -/
theorem transferSizeBar_le_costEnvelope {U CAE Cd g K Arad : ℝ} {E : BlockMat d}
    {m0 : Mat d} {j : ℤ} (hU : 0 ≤ U) (hCAE : 0 ≤ CAE) (hCd : 0 ≤ Cd) (hg1 : g < 1)
    (hkap : kappaRef E ≤ 6 * aspectRatio E) (hPi : 1 ≤ aspectRatio E)
    (hecc : 0 ≤ witnessEccentricity m0)
    (hrad : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hgauge : transferGauge g K j ≤ (2 : ℝ) ^ g / (1 - g)) :
    transferSizeBar U CAE Cd g K E m0 j ≤
      6 * U * CAE * Cd * aspectRatio E * (2 + aspectRatio E) ^ (2 * Arad) *
        zetaG g * ((2 : ℝ) ^ g / (1 - g)) := by
  have hb : (0 : ℝ) ≤ 2 + aspectRatio E := by linarith only [hPi]
  have hzeta : (0 : ℝ) < zetaG g := Transport.zero_lt_zetaG hg1
  have hgam : (0 : ℝ) < transferGauge g K j := zero_lt_transferGauge hg1 K j
  have hUCd : (0 : ℝ) ≤ U * CAE * Cd := mul_nonneg (mul_nonneg hU hCAE) hCd
  have h6Pi : (0 : ℝ) ≤ 6 * aspectRatio E := by linarith only [hPi]
  have hrp : (0 : ℝ) ≤ (2 + aspectRatio E) ^ (2 * Arad) := Real.rpow_nonneg hb _
  have hsq : witnessEccentricity m0 ^ 2 ≤ (2 + aspectRatio E) ^ (2 * Arad) := by
    have h2 : (2 + aspectRatio E) ^ (2 * Arad)
        = ((2 + aspectRatio E) ^ Arad) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((2 + aspectRatio E) ^ Arad) 2, ← Real.rpow_mul hb]
      congr 1
      push_cast
      ring
    rw [h2]
    exact pow_le_pow_left₀ hecc hrad 2
  have hA : (0 : ℝ) ≤ U * CAE * Cd * witnessEccentricity m0 ^ 2 * zetaG g *
      transferGauge g K j :=
    mul_nonneg (mul_nonneg (mul_nonneg hUCd (sq_nonneg _)) hzeta.le) hgam.le
  have hB : (0 : ℝ) ≤ U * CAE * Cd * zetaG g * transferGauge g K j *
      (6 * aspectRatio E) :=
    mul_nonneg (mul_nonneg (mul_nonneg hUCd hzeta.le) hgam.le) h6Pi
  have hC : (0 : ℝ) ≤ U * CAE * Cd * zetaG g * (6 * aspectRatio E) *
      (2 + aspectRatio E) ^ (2 * Arad) :=
    mul_nonneg (mul_nonneg (mul_nonneg hUCd hzeta.le) h6Pi) hrp
  rw [transferSizeBar]
  calc U * CAE * Cd * kappaRef E * witnessEccentricity m0 ^ 2 * zetaG g *
        transferGauge g K j
      = U * CAE * Cd * witnessEccentricity m0 ^ 2 * zetaG g * transferGauge g K j *
          kappaRef E := by ring
    _ ≤ U * CAE * Cd * witnessEccentricity m0 ^ 2 * zetaG g * transferGauge g K j *
          (6 * aspectRatio E) := mul_le_mul_of_nonneg_left hkap hA
    _ = U * CAE * Cd * zetaG g * transferGauge g K j * (6 * aspectRatio E) *
          witnessEccentricity m0 ^ 2 := by ring
    _ ≤ U * CAE * Cd * zetaG g * transferGauge g K j * (6 * aspectRatio E) *
          (2 + aspectRatio E) ^ (2 * Arad) := mul_le_mul_of_nonneg_left hsq hB
    _ = U * CAE * Cd * zetaG g * (6 * aspectRatio E) *
          (2 + aspectRatio E) ^ (2 * Arad) * transferGauge g K j := by ring
    _ ≤ U * CAE * Cd * zetaG g * (6 * aspectRatio E) *
          (2 + aspectRatio E) ^ (2 * Arad) * ((2 : ℝ) ^ g / (1 - g)) :=
        mul_le_mul_of_nonneg_left hgauge hC
    _ = 6 * U * CAE * Cd * aspectRatio E * (2 + aspectRatio E) ^ (2 * Arad) *
          zetaG g * ((2 : ℝ) ^ g / (1 - g)) := by ring

/-- The truncated logarithm of a discounted comparison size lies below the one
read on the common envelope at the smaller tolerance.  This is the single step
by which each of the two gaps is estimated. -/
theorem max_logb_transferSizeBar_le {U CAE Cd g K Arad eta etaPlus etaMinus : ℝ}
    {E : BlockMat d} {m0 : Mat d} {j : ℤ} (hU : 0 ≤ U) (hCAE : 0 ≤ CAE) (hCd : 0 ≤ Cd)
    (hg1 : g < 1) (hkap : kappaRef E ≤ 6 * aspectRatio E) (hPi : 1 ≤ aspectRatio E)
    (hecc : 0 ≤ witnessEccentricity m0)
    (hrad : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hgauge : transferGauge g K j ≤ (2 : ℝ) ^ g / (1 - g))
    (hetaPlus : 0 < etaPlus) (hetaMinus : 0 < etaMinus) (heta : 0 < eta)
    (hmin : min etaPlus etaMinus ≤ eta) :
    max 0 (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 j / eta)) ≤
      max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
          (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)))) := by
  have hm : (0 : ℝ) < min etaPlus etaMinus := lt_min hetaPlus hetaMinus
  have hT0 : 0 ≤ transferSizeBar U CAE Cd g K E m0 j :=
    zero_le_transferSizeBar hU hCAE hCd hg1
  have hTE := transferSizeBar_le_costEnvelope (Arad := Arad) hU hCAE hCd hg1 hkap hPi
    hecc hrad hgauge
  have hEnv0 : (0 : ℝ) ≤ 6 * U * CAE * Cd * aspectRatio E *
      (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)) :=
    le_trans hT0 hTE
  have hWeq : 6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
      (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)) *
        min etaPlus etaMinus
      = 6 * U * CAE * Cd * aspectRatio E * (2 + aspectRatio E) ^ (2 * Arad) *
          zetaG g * ((2 : ℝ) ^ g / (1 - g)) := by
    field_simp
  have hW0 : (0 : ℝ) ≤ 6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
      (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)) := by
    refine le_of_mul_le_mul_right ?_ hm
    rw [zero_mul, hWeq]
    exact hEnv0
  refine max_logb_le_max_logb (div_nonneg hT0 heta.le) ?_
  rw [div_le_iff₀ heta]
  calc transferSizeBar U CAE Cd g K E m0 j
      ≤ 6 * U * CAE * Cd * aspectRatio E * (2 + aspectRatio E) ^ (2 * Arad) *
          zetaG g * ((2 : ℝ) ^ g / (1 - g)) := hTE
    _ = 6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
          (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)) *
          min etaPlus etaMinus := hWeq.symm
    _ ≤ 6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
          (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)) * eta :=
        mul_le_mul_of_nonneg_left hmin hW0

/-! ## The two cost bounds -/

/-- **The exact two-gap cost** of `e.response.transfer.gaps`.  Each gap is below
its truncated
logarithm plus two, each truncated logarithm is below the one read on the common
envelope at the smaller tolerance, and the two gaps are paid together. -/
theorem exact_cost {U CAE Cd g K Arad etaPlus etaMinus : ℝ} {E : BlockMat d}
    {m0 : Mat d} {t ment l r : ℤ} (hU : 0 ≤ U) (hCAE : 0 ≤ CAE) (hCd : 0 ≤ Cd)
    (hg1 : g < 1) (hkap : kappaRef E ≤ 6 * aspectRatio E) (hPi : 1 ≤ aspectRatio E)
    (hecc : 0 ≤ witnessEccentricity m0)
    (hrad : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hgt : transferGauge g K t ≤ (2 : ℝ) ^ g / (1 - g))
    (hgm : transferGauge g K ment ≤ (2 : ℝ) ^ g / (1 - g))
    (hetaPlus : 0 < etaPlus) (hetaMinus : 0 < etaMinus)
    (hl : l = ⌈max 1 (max 0
      (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 t / etaPlus)))⌉)
    (hr : r = ⌈max 1 (max 0
      (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 ment / etaMinus)))⌉) :
    (l : ℝ) + (r : ℝ) ≤
      4 + 2 * max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
          (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)))) := by
  have hlc : (l : ℝ) ≤
      max 0 (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 t / etaPlus)) + 2 := by
    rw [hl]; exact gapCeil_le_add_two _
  have hrc : (r : ℝ) ≤
      max 0 (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 ment / etaMinus)) + 2 := by
    rw [hr]; exact gapCeil_le_add_two _
  have hlt := max_logb_transferSizeBar_le (Arad := Arad) (j := t) (eta := etaPlus)
    hU hCAE hCd hg1 hkap hPi hecc hrad hgt hetaPlus hetaMinus hetaPlus
    (min_le_left _ _)
  have hrt := max_logb_transferSizeBar_le (Arad := Arad) (j := ment) (eta := etaMinus)
    hU hCAE hCd hg1 hkap hPi hecc hrad hgm hetaPlus hetaMinus hetaMinus
    (min_le_right _ _)
  linarith only [hlc, hrc, hlt, hrt]

/-- The exhibited gap constant is positive: the truncation is nonnegative and the
radius exponent is nonnegative, so the constant is at least four. -/
theorem zero_lt_gapConst {U CAE Cd g Arad etaPlus etaMinus : ℝ} (hArad : 0 ≤ Arad) :
    0 < 4 + 2 * max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
          ((2 : ℝ) ^ g / (1 - g)))) + 2 * (1 + 2 * Arad) := by
  have h0 : (0 : ℝ) ≤ max 0 (Real.logb 3
      (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
        ((2 : ℝ) ^ g / (1 - g)))) := le_max_left _ _
  linarith only [h0, hArad]

/-- **The logarithmic two-gap cost** of `e.response.transfer.gaps`.  The
envelope splits as a
constant free of the reference block times `Π(2 + Π)^{2A_rad}`; the logarithm of
the second factor is at most `(1 + 2A_rad)log_3(2 + Π)`, and `log_3(2 + Π) ≥ 1`
absorbs the additive constant. -/
theorem logarithmic_cost {U CAE Cd g K Arad etaPlus etaMinus : ℝ} {E : BlockMat d}
    {m0 : Mat d} {t ment l r : ℤ} (hU : 0 < U) (hCAE : 0 < CAE) (hCd : 0 < Cd)
    (hg1 : g < 1) (hkap : kappaRef E ≤ 6 * aspectRatio E) (hPi : 1 ≤ aspectRatio E)
    (hecc : 0 ≤ witnessEccentricity m0) (hArad : 0 ≤ Arad)
    (hrad : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hgt : transferGauge g K t ≤ (2 : ℝ) ^ g / (1 - g))
    (hgm : transferGauge g K ment ≤ (2 : ℝ) ^ g / (1 - g))
    (hetaPlus : 0 < etaPlus) (hetaMinus : 0 < etaMinus)
    (hl : l = ⌈max 1 (max 0
      (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 t / etaPlus)))⌉)
    (hr : r = ⌈max 1 (max 0
      (Real.logb 3 (transferSizeBar U CAE Cd g K E m0 ment / etaMinus)))⌉) :
    (l : ℝ) + (r : ℝ) ≤
      (4 + 2 * max 0 (Real.logb 3
          (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
            ((2 : ℝ) ^ g / (1 - g)))) + 2 * (1 + 2 * Arad)) *
        Real.logb 3 (2 + aspectRatio E) := by
  have hm : (0 : ℝ) < min etaPlus etaMinus := lt_min hetaPlus hetaMinus
  have hb : (0 : ℝ) < 2 + aspectRatio E := by linarith only [hPi]
  have hPi0 : (0 : ℝ) < aspectRatio E := by linarith only [hPi]
  have hzeta : (0 : ℝ) < zetaG g := Transport.zero_lt_zetaG hg1
  have hquot : (0 : ℝ) < (2 : ℝ) ^ g / (1 - g) :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) g) (by linarith only [hg1])
  have hrp : (0 : ℝ) < (2 + aspectRatio E) ^ (2 * Arad) := Real.rpow_pos_of_pos hb _
  have hK0 : (0 : ℝ) < 6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
      ((2 : ℝ) ^ g / (1 - g)) :=
    mul_pos (mul_pos (div_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hU)
      hCAE) hCd) hm) hzeta) hquot
  have hexact := exact_cost (Arad := Arad) hU.le hCAE.le hCd.le hg1 hkap hPi hecc hrad
    hgt hgm hetaPlus hetaMinus hl hr
  have hL1 : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 3) hb, Real.rpow_one]
    linarith only [hPi]
  have hLPi : Real.logb 3 (aspectRatio E) ≤ Real.logb 3 (2 + aspectRatio E) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3) hPi0
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
  have hLrp : Real.logb 3 ((2 + aspectRatio E) ^ (2 * Arad))
      = 2 * Arad * Real.logb 3 (2 + aspectRatio E) :=
    Real.logb_rpow_eq_mul_logb_of_pos hb
  have hsplit : Real.logb 3
      (6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
        (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)))
      = Real.logb 3 (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
          ((2 : ℝ) ^ g / (1 - g))) + Real.logb 3 (aspectRatio E) +
        Real.logb 3 ((2 + aspectRatio E) ^ (2 * Arad)) := by
    have heq : 6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
        (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g))
        = 6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
            ((2 : ℝ) ^ g / (1 - g)) * aspectRatio E *
          (2 + aspectRatio E) ^ (2 * Arad) := by ring
    rw [heq, Real.logb_mul (ne_of_gt (mul_pos hK0 hPi0)) (ne_of_gt hrp),
      Real.logb_mul (ne_of_gt hK0) (ne_of_gt hPi0)]
  have hC0 : (0 : ℝ) ≤ max 0 (Real.logb 3
      (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
        ((2 : ℝ) ^ g / (1 - g)))) := le_max_left _ _
  have hup : Real.logb 3 (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
      ((2 : ℝ) ^ g / (1 - g))) ≤
      max 0 (Real.logb 3 (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
        ((2 : ℝ) ^ g / (1 - g)))) := le_max_right _ _
  have hnn : (0 : ℝ) ≤ (1 + 2 * Arad) * Real.logb 3 (2 + aspectRatio E) :=
    mul_nonneg (by linarith only [hArad]) (by linarith only [hL1])
  have hmax : max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * aspectRatio E *
          (2 + aspectRatio E) ^ (2 * Arad) * zetaG g * ((2 : ℝ) ^ g / (1 - g)))) ≤
      max 0 (Real.logb 3 (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
          ((2 : ℝ) ^ g / (1 - g)))) +
        (1 + 2 * Arad) * Real.logb 3 (2 + aspectRatio E) := by
    refine max_le (by linarith only [hC0, hnn]) ?_
    rw [hsplit, hLrp]
    linarith only [hup, hLPi]
  have hcabs : 4 + 2 * max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
          ((2 : ℝ) ^ g / (1 - g)))) ≤
      (4 + 2 * max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
          ((2 : ℝ) ^ g / (1 - g))))) * Real.logb 3 (2 + aspectRatio E) := by
    have hc : (0 : ℝ) ≤ 4 + 2 * max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
          ((2 : ℝ) ^ g / (1 - g)))) := by linarith only [hC0]
    calc 4 + 2 * max 0 (Real.logb 3
          (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
            ((2 : ℝ) ^ g / (1 - g))))
        = (4 + 2 * max 0 (Real.logb 3
            (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
              ((2 : ℝ) ^ g / (1 - g))))) * 1 := (mul_one _).symm
      _ ≤ (4 + 2 * max 0 (Real.logb 3
            (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
              ((2 : ℝ) ^ g / (1 - g))))) * Real.logb 3 (2 + aspectRatio E) :=
          mul_le_mul_of_nonneg_left hL1 hc
  linarith only [hexact, hmax, hcabs]

end

end Persistence
end HighContrast
end Homogenization
