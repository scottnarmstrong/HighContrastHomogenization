/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.Exponents

/-!
# Admissibility of the response-window exponents

The response window fixes its exponents `a`, `Q`, `ρ_max`, `ρ_dr` by the
formulas of `e.scale.selection.Q.choice`, the same formulas already carried for
the fixed-history exponents.  The admissibility clause of the response window is
therefore not a hypothesis but a fact about those carriers:
for `d ≥ 2` and `0 ≤ g < 1` the integer `Q` is even and at least twelve, the
exponents obey `g < ρ_max < (1+g)/2`, and `a ≤ Qρ_max - d`.  Together these say
that the exponents fixed by `e.scale.selection.Q.choice` lie in the admissible
region.

The strict upper bound `ρ_max < 3/2`, a consequence of `ρ_max < (1+g)/2` and
`g < 1`, is the one that makes negative the row exponent of the source
allocation in the smallness of the all-earlier source row.
-/

namespace Homogenization
namespace HighContrast
namespace Response

noncomputable section

variable {d : ℕ} {g : ℝ}

/-- The response exponent `Q = 2⌈2(d+1)/(1-g)⌉` is even. -/
theorem initExpQ_even : Even (initExpQ d g) :=
  InitializationExponents.initExpQ_even d g

/-- In dimension at least two and below the source exponent one, the response
exponent is at least twelve. -/
theorem twelve_le_initExpQ (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    12 ≤ initExpQ d g := by
  obtain ⟨hg0, hg1⟩ := hg
  have hden : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnum : (6 : ℝ) ≤ 2 * ((d : ℝ) + 1) := by linarith only [hd']
  have hkey : (6 : ℝ) ≤ 2 * ((d : ℝ) + 1) / (1 - g) := by
    rw [le_div_iff₀ hden]
    linarith only [hg0, hnum]
  have hceil : (6 : ℝ) ≤ (⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ : ℝ) :=
    le_trans hkey (Nat.le_ceil _)
  have hceil' : 6 ≤ ⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ := by exact_mod_cast hceil
  rw [initExpQ]
  omega

/-- The response exponent is positive as a real number. -/
theorem zero_lt_initExpQ (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    (0 : ℝ) < (initExpQ d g : ℝ) := by
  have h : (12 : ℝ) ≤ (initExpQ d g : ℝ) := by exact_mod_cast twelve_le_initExpQ hd hg
  linarith only [h]

/-- The response exponent `a = (1-g)/4` is positive below the source exponent
one. -/
theorem zero_lt_initExpA (hg : g ∈ Set.Ico (0 : ℝ) 1) : 0 < initExpA g := by
  exact InitializationExponents.initExpA_pos hg.2

private theorem lt_initExpRhoMax_of_two_le (d : ℕ) (_hd : 2 ≤ d) {g : ℝ}
    (hg : g < 1) : g < initExpRhoMax d g :=
  InitializationExponents.lt_initExpRhoMax d hg

/-- The lower half of the admissible exponent region: `g < ρ_max`. -/
theorem lt_initExpRhoMax (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    g < initExpRhoMax d g := by
  exact lt_initExpRhoMax_of_two_le d hd hg.2

/-- The exponent `ρ_max` is positive. -/
theorem zero_lt_initExpRhoMax (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < initExpRhoMax d g :=
  lt_of_le_of_lt hg.1 (lt_initExpRhoMax hd hg)

/-- The upper half of the admissible exponent region: `ρ_max < (1+g)/2`.  The
ceiling in `Q` is used only through `Q(1-g) ≥ 4(d+1)`. -/
theorem initExpRhoMax_lt_half_add (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    initExpRhoMax d g < (1 + g) / 2 := by
  obtain ⟨hg0, hg1⟩ := hg
  have hden : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hQpos : (0 : ℝ) < (initExpQ d g : ℝ) := zero_lt_initExpQ hd ⟨hg0, hg1⟩
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hceil := Nat.le_ceil (2 * ((d : ℝ) + 1) / (1 - g))
  have hQeq : (initExpQ d g : ℝ) = 2 * (⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ : ℝ) := by
    rw [initExpQ, Nat.cast_mul, Nat.cast_ofNat]
  have hprod : 2 * ((d : ℝ) + 1) / (1 - g) * (1 - g) = 2 * ((d : ℝ) + 1) :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hstep : 2 * ((d : ℝ) + 1) ≤ (⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ : ℝ) * (1 - g) := by
    have h := mul_le_mul_of_nonneg_right hceil (le_of_lt hden)
    linarith only [h, hprod]
  have hQ2 : 4 * ((d : ℝ) + 1) ≤ (initExpQ d g : ℝ) * (1 - g) := by
    rw [hQeq]
    linarith only [hstep]
  have hfrac : ((d : ℝ) + initExpA g) / (initExpQ d g : ℝ) < (1 - g) / 2 := by
    rw [div_lt_iff₀ hQpos, initExpA]
    linarith only [hQ2, hg0, hd']
  rw [initExpRhoMax]
  linarith only [hfrac]

/-- The exponent `ρ_max` is strictly below `3/2`, which is what makes the
all-earlier row exponent of the source allocation negative. -/
theorem initExpRhoMax_lt_three_halves (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    initExpRhoMax d g < 3 / 2 := by
  have h := initExpRhoMax_lt_half_add hd hg
  have hg1 := hg.2
  linarith only [h, hg1]

/-- The remaining admissibility clause `a ≤ Qρ_max - d`, with equality exactly
at `g = 0`. -/
theorem initExpA_le_mul_sub (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    initExpA g ≤ (initExpQ d g : ℝ) * initExpRhoMax d g - (d : ℝ) := by
  have hQpos : (0 : ℝ) < (initExpQ d g : ℝ) := zero_lt_initExpQ hd hg
  have hexp : (initExpQ d g : ℝ) * initExpRhoMax d g
      = (initExpQ d g : ℝ) * g + ((d : ℝ) + initExpA g) := by
    rw [initExpRhoMax]
    field_simp
  have hgQ : 0 ≤ (initExpQ d g : ℝ) * g := mul_nonneg (le_of_lt hQpos) hg.1
  linarith only [hexp, hgQ]

end

end Response
end HighContrast
end Homogenization
