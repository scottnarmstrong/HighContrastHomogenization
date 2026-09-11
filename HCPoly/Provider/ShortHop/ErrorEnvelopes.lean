/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects

/-!
# The six error envelopes of the short test

The successful short test (`p.successful.short.bridge`) chooses its
five thresholds in a fixed order, and the choice is legitimate because the six
continuous error functions it reads are monotone in each of their five
arguments, vanish at the origin in the two drift envelopes, and collapse there
to the four scale-only floors `e_+^{(0)}`, `e_-^{(0)}`, `η_br^{(0)}`,
`𝔡_new^{(0)}` of the proof.

This file proves exactly those three facts — monotonicity, the values at the
origin, and continuity along the diagonal — for
`shortDriftNew`, `shortDriftTerm`, `shortErrUpper`, `shortErrLower`,
`shortBridgeErr` and `shortNewDrift`.  Nothing here is specific to the law:
the envelopes are deterministic functions of the two constants, the drift
exponent and the hop length.

The standing hypotheses are the ones the proposition itself carries: the
two-grid constant and the rounded-hop constant are nonnegative, and the hop
length is large enough that the denominator `1 - CK_hop3^{-ℓ₀}` of the lower
envelope stays at or above one half, which is the second requirement among the
constants fixed for the bridge test.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

noncomputable section

variable {d : ℕ} {C Khop rhoDr : ℝ} {l0 : ℤ}

/-! ## The denominator of the lower envelope -/

/-- Under the second constants requirement the denominator of the lower
comparison envelope is at least one half, hence positive. -/
theorem half_le_one_sub_denom (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2) :
    1 / 2 ≤ 1 - C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) := by
  linarith only [hden]

/-- The coefficient of the lower comparison envelope is nonnegative. -/
theorem lower_coeff_nonneg (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2) :
    0 ≤ C * Khop / (1 - C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) :=
  div_nonneg (mul_nonneg hC hK) (by linarith only [half_le_one_sub_denom hden])

/-! ## Nonnegativity -/

/-- The new-scale drift envelope is nonnegative on the box. -/
theorem shortDriftNew_nonneg {b delta : ℝ} (hb : 0 ≤ b) (hdelta : 0 ≤ delta) :
    0 ≤ shortDriftNew d rhoDr l0 b delta := by
  have hone : (1 : ℝ) ≤ (1 + delta) ^ d := one_le_pow₀ (by linarith only [hdelta])
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) := by positivity
  have h₁ : 0 ≤ (1 + delta) ^ d * (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) * b := by
    have : (0 : ℝ) ≤ (1 + delta) ^ d := by linarith only [hone]
    positivity
  have h₂ : 0 ≤ 2 * (d : ℝ) * ((1 + delta) ^ d - 1) := by
    have hnn : (0 : ℝ) ≤ (1 + delta) ^ d - 1 := by linarith only [hone]
    positivity
  simpa only [shortDriftNew] using add_nonneg h₁ h₂

/-- The upper comparison envelope is nonnegative on the box. -/
theorem shortErrUpper_nonneg (hC : 0 ≤ C) (hK : 0 ≤ Khop) {b delta R1 : ℝ}
    (hb : 0 ≤ b) (hdelta : 0 ≤ delta) (hR1 : 0 ≤ R1) :
    0 ≤ shortErrUpper d C Khop rhoDr l0 b delta R1 := by
  have hdn : 0 ≤ shortDriftNew d rhoDr l0 b delta := shortDriftNew_nonneg hb hdelta
  have hCK : 0 ≤ C * Khop := mul_nonneg hC hK
  have hbr : 0 ≤ (3 : ℝ) ^ (-(l0 : ℝ)) +
      (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) * shortDriftNew d rhoDr l0 b delta := by
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (-(l0 : ℝ)) := by positivity
    have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) := by positivity
    nlinarith only [h1, h2, hdn]
  simpa only [shortErrUpper] using add_nonneg (mul_nonneg hCK hbr) hR1

/-! ## Monotonicity -/

/-- The new-scale drift envelope is monotone in the drift bound and in the
determinant tolerance. -/
theorem shortDriftNew_mono {b b' delta delta' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hdelta : 0 ≤ delta) (hdd : delta ≤ delta') :
    shortDriftNew d rhoDr l0 b delta ≤ shortDriftNew d rhoDr l0 b' delta' := by
  have hd1 : (0 : ℝ) ≤ 1 + delta := by linarith only [hdelta]
  have hd2 : (0 : ℝ) ≤ 1 + delta' := by linarith only [hdelta, hdd]
  have hpow : (1 + delta) ^ d ≤ (1 + delta') ^ d :=
    pow_le_pow_left₀ hd1 (by linarith only [hdd]) d
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) := by positivity
  have hp2 : (0 : ℝ) ≤ (1 + delta') ^ d := pow_nonneg hd2 d
  have h₁ : (1 + delta) ^ d * (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) * b ≤
      (1 + delta') ^ d * (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) * b' :=
    mul_le_mul (mul_le_mul_of_nonneg_right hpow h3.le) hbb hb (mul_nonneg hp2 h3.le)
  have h₂ : 2 * (d : ℝ) * ((1 + delta) ^ d - 1) ≤ 2 * (d : ℝ) * ((1 + delta') ^ d - 1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hpow]) (by positivity)
  simpa only [shortDriftNew] using add_le_add h₁ h₂

/-- The terminal-scale drift envelope is monotone in the drift bound and in the
determinant tolerance. -/
theorem shortDriftTerm_mono {b b' delta delta' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hdelta : 0 ≤ delta) (hdd : delta ≤ delta') :
    shortDriftTerm d rhoDr l0 b delta ≤ shortDriftTerm d rhoDr l0 b' delta' := by
  have hd1 : (0 : ℝ) ≤ 1 + delta := by linarith only [hdelta]
  have hd2 : (0 : ℝ) ≤ 1 + delta' := by linarith only [hdelta, hdd]
  have hpow : (1 + delta) ^ d ≤ (1 + delta') ^ d :=
    pow_le_pow_left₀ hd1 (by linarith only [hdd]) d
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-2 * rhoDr * (l0 : ℝ)) := by positivity
  have hp2 : (0 : ℝ) ≤ (1 + delta') ^ d := pow_nonneg hd2 d
  have h₁ : (1 + delta) ^ d * (3 : ℝ) ^ (-2 * rhoDr * (l0 : ℝ)) * b ≤
      (1 + delta') ^ d * (3 : ℝ) ^ (-2 * rhoDr * (l0 : ℝ)) * b' :=
    mul_le_mul (mul_le_mul_of_nonneg_right hpow h3.le) hbb hb (mul_nonneg hp2 h3.le)
  have h₂ : 2 * (d : ℝ) * ((1 + delta) ^ d - 1) ≤ 2 * (d : ℝ) * ((1 + delta') ^ d - 1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hpow]) (by positivity)
  simpa only [shortDriftTerm] using add_le_add h₁ h₂

/-- The upper comparison envelope is monotone in all three arguments. -/
theorem shortErrUpper_mono (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    {b b' delta delta' R1 R1' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hdelta : 0 ≤ delta) (hdd : delta ≤ delta') (hRR : R1 ≤ R1') :
    shortErrUpper d C Khop rhoDr l0 b delta R1 ≤
      shortErrUpper d C Khop rhoDr l0 b' delta' R1' := by
  have hdn := shortDriftNew_mono (d := d) (rhoDr := rhoDr) (l0 := l0) hb hbb hdelta hdd
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) := by positivity
  have hbr : (3 : ℝ) ^ (-(l0 : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) * shortDriftNew d rhoDr l0 b delta ≤
      (3 : ℝ) ^ (-(l0 : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) * shortDriftNew d rhoDr l0 b' delta' := by
    linarith only [mul_le_mul_of_nonneg_left hdn h2.le]
  simpa only [shortErrUpper] using
    add_le_add (mul_le_mul_of_nonneg_left hbr (mul_nonneg hC hK)) hRR

/-- The lower comparison envelope is monotone in all three arguments. -/
theorem shortErrLower_mono (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2)
    {b b' delta delta' R2 R2' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hdelta : 0 ≤ delta) (hdd : delta ≤ delta') (hRR : R2 ≤ R2') :
    shortErrLower d C Khop rhoDr l0 b delta R2 ≤
      shortErrLower d C Khop rhoDr l0 b' delta' R2' := by
  have hdt := shortDriftTerm_mono (d := d) (rhoDr := rhoDr) (l0 := l0) hb hbb hdelta hdd
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) := by positivity
  have hbr : (3 : ℝ) ^ (-(l0 : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) * shortDriftTerm d rhoDr l0 b delta ≤
      (3 : ℝ) ^ (-(l0 : ℝ)) +
        (3 : ℝ) ^ (-(1 - rhoDr) * (l0 : ℝ)) * shortDriftTerm d rhoDr l0 b' delta' := by
    linarith only [mul_le_mul_of_nonneg_left hdt h2.le]
  simpa only [shortErrLower] using
    add_le_add (mul_le_mul_of_nonneg_left hbr (lower_coeff_nonneg hC hK hden)) hRR

/-- The bridge-error envelope is monotone in all four arguments. -/
theorem shortBridgeErr_mono (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2)
    {b b' delta delta' R1 R1' R2 R2' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hdelta : 0 ≤ delta) (hdd : delta ≤ delta') (hR1 : 0 ≤ R1) (hRR1 : R1 ≤ R1')
    (hRR2 : R2 ≤ R2') :
    shortBridgeErr d C Khop rhoDr l0 b delta R1 R2 ≤
      shortBridgeErr d C Khop rhoDr l0 b' delta' R1' R2' := by
  have hlow := shortErrLower_mono (d := d) (rhoDr := rhoDr) hC hK hden hb hbb hdelta hdd hRR2
  have hup := shortErrUpper_mono (d := d) (rhoDr := rhoDr) (l0 := l0) hC hK hb hbb hdelta hdd hRR1
  have hup0 := shortErrUpper_nonneg (d := d) (rhoDr := rhoDr) (l0 := l0) hC hK hb hdelta hR1
  have hpow : (1 + delta) ^ d ≤ (1 + delta') ^ d :=
    pow_le_pow_left₀ (by linarith only [hdelta]) (by linarith only [hdd]) d
  have hsnd :
      (1 + shortErrUpper d C Khop rhoDr l0 b delta R1) * (1 + delta) ^ d - 1 ≤
        (1 + shortErrUpper d C Khop rhoDr l0 b' delta' R1') * (1 + delta') ^ d - 1 := by
    have hmul := mul_le_mul (by linarith only [hup] :
        1 + shortErrUpper d C Khop rhoDr l0 b delta R1 ≤
          1 + shortErrUpper d C Khop rhoDr l0 b' delta' R1')
      hpow (by positivity) (by linarith only [hup, hup0])
    linarith only [hmul]
  exact max_le_max hlow hsnd

/-- The new-grid drift envelope is monotone in all four arguments. -/
theorem shortNewDrift_mono (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2)
    {b b' delta delta' R2 R2' R3 R3' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hdelta : 0 ≤ delta) (hdd : delta ≤ delta') (hRR2 : R2 ≤ R2') (hRR3 : R3 ≤ R3') :
    shortNewDrift d C Khop rhoDr l0 b delta R2 R3 ≤
      shortNewDrift d C Khop rhoDr l0 b' delta' R2' R3' := by
  have hlow := shortErrLower_mono (d := d) (rhoDr := rhoDr) hC hK hden hb hbb hdelta hdd hRR2
  have hdt := shortDriftTerm_mono (d := d) (rhoDr := rhoDr) (l0 := l0) hb hbb hdelta hdd
  have hcoef : (0 : ℝ) ≤ (1 + Khop) * (3 : ℝ) ^ (2 * rhoDr * (l0 : ℝ)) := by positivity
  have hterm := mul_le_mul_of_nonneg_left hdt hcoef
  simpa only [shortNewDrift] using
    mul_le_mul_of_nonneg_left (by linarith only [hlow, hterm, hRR3]) hC

/-! ## The values at the origin -/

/-- The terminal-scale drift envelope vanishes at the origin. -/
theorem shortDriftTerm_zero : shortDriftTerm d rhoDr l0 0 0 = 0 := by
  simp [shortDriftTerm]

/-- At the origin the upper comparison envelope is the scale-only floor
`e_+^{(0)}(ℓ₀) = CK_hop3^{-ℓ₀}`. -/
theorem shortErrUpper_zero :
    shortErrUpper d C Khop rhoDr l0 0 0 0 = C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) := by
  simp [shortErrUpper, shortDriftNew]

/-- At the origin the lower comparison envelope is the scale-only floor
`e_-^{(0)}(ℓ₀) = CK_hop3^{-ℓ₀}(1 - CK_hop3^{-ℓ₀})^{-1}`. -/
theorem shortErrLower_zero :
    shortErrLower d C Khop rhoDr l0 0 0 0 =
      C * Khop / (1 - C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) * (3 : ℝ) ^ (-(l0 : ℝ)) := by
  simp [shortErrLower, shortDriftTerm]

/-- The lower floor is at most twice the upper floor once the denominator is at
least one half. -/
theorem shortErrLower_zero_le (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2) :
    shortErrLower d C Khop rhoDr l0 0 0 0 ≤ 2 * (C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) := by
  have hpos : (0 : ℝ) < 1 - C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) := by
    linarith only [half_le_one_sub_denom hden]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(l0 : ℝ)) := by positivity
  have hCK : 0 ≤ C * Khop := mul_nonneg hC hK
  have hA : 0 ≤ C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) := mul_nonneg hCK h3.le
  have hprod : 0 ≤ C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) *
      (1 / 2 - C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) :=
    mul_nonneg hA (by linarith only [hden])
  rw [shortErrLower_zero (d := d) (rhoDr := rhoDr), div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith only [hprod]

/-- At the origin the bridge-error envelope is at most twice the upper floor. -/
theorem shortBridgeErr_zero_le (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2) :
    shortBridgeErr d C Khop rhoDr l0 0 0 0 0 ≤
      2 * (C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) := by
  have hlow := shortErrLower_zero_le (d := d) (rhoDr := rhoDr) hC hK hden
  have hup : (1 + shortErrUpper d C Khop rhoDr l0 0 0 0) * (1 + (0 : ℝ)) ^ d - 1 ≤
      2 * (C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) := by
    have hCK : 0 ≤ C * Khop := mul_nonneg hC hK
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(l0 : ℝ)) := by positivity
    have hA : 0 ≤ C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) := mul_nonneg hCK h3.le
    rw [shortErrUpper_zero (d := d) (rhoDr := rhoDr)]
    simp only [add_zero, one_pow, mul_one]
    linarith only [hA]
  exact max_le hlow hup

/-- At the origin the new-grid drift envelope is at most `C(2C + 1)` times the
upper floor. -/
theorem shortNewDrift_zero_le (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2) :
    shortNewDrift d C Khop rhoDr l0 0 0 0 0 ≤
      (2 * C + 1) * (C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) := by
  have hlow := shortErrLower_zero_le (d := d) (rhoDr := rhoDr) hC hK hden
  have hdt : shortDriftTerm d rhoDr l0 0 0 = 0 := shortDriftTerm_zero
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(l0 : ℝ)) := by positivity
  have hbody : shortErrLower d C Khop rhoDr l0 0 0 0 + Khop * (3 : ℝ) ^ (-(l0 : ℝ)) +
      (1 + Khop) * (3 : ℝ) ^ (2 * rhoDr * (l0 : ℝ)) * shortDriftTerm d rhoDr l0 0 0 + 0 ≤
      2 * (C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) + Khop * (3 : ℝ) ^ (-(l0 : ℝ)) := by
    rw [hdt]
    simp only [mul_zero, add_zero]
    linarith only [hlow]
  have hmul := mul_le_mul_of_nonneg_left hbody hC
  have hgoal : C * (2 * (C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) + Khop * (3 : ℝ) ^ (-(l0 : ℝ))) =
      (2 * C + 1) * (C * Khop * (3 : ℝ) ^ (-(l0 : ℝ))) := by ring
  simpa only [shortNewDrift] using hmul.trans_eq hgoal

/-! ## Continuity along the diagonal -/

/-- The bridge-error envelope is continuous along the diagonal of its four
arguments. -/
theorem continuous_shortBridgeErr_diag :
    Continuous fun t : ℝ => shortBridgeErr d C Khop rhoDr l0 t t t t := by
  unfold shortBridgeErr shortErrLower shortErrUpper shortDriftNew shortDriftTerm
  fun_prop

/-- The new-grid drift envelope is continuous along the diagonal of its four
arguments. -/
theorem continuous_shortNewDrift_diag :
    Continuous fun t : ℝ => shortNewDrift d C Khop rhoDr l0 t t t t := by
  unfold shortNewDrift shortErrLower shortDriftTerm
  fun_prop

end

end ShortHop
end HighContrast
end Homogenization
