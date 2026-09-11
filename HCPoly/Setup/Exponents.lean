/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SourceObjects

/-!
# Arithmetic of the initialization exponents

The fixed initialization exponents have four elementary properties that only
require the growth exponent to be strictly below one.  They are recorded here
for the initialization, selection, response, and entry layers to share.
-/

namespace Homogenization.HighContrast.InitializationExponents

noncomputable section

/-- The moment exponent chosen for initialization is even. -/
theorem initExpQ_even (d : ℕ) (g : ℝ) : Even (initExpQ d g) := by
  rw [initExpQ]
  exact even_two_mul _

/-- The moment exponent chosen for initialization is at least two whenever the
growth exponent is strictly below one. -/
theorem two_le_initExpQ (d : ℕ) {g : ℝ} (hg : g < 1) : 2 ≤ initExpQ d g := by
  have hden : (0 : ℝ) < 1 - g := by linarith only [hg]
  have hnum : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by positivity
  have hpos : 0 < 2 * ((d : ℝ) + 1) / (1 - g) := div_pos hnum hden
  have hceil : 1 ≤ ⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ :=
    Nat.one_le_ceil_iff.mpr hpos
  rw [initExpQ]
  omega

/-- The history exponent is positive whenever the growth exponent is strictly
below one. -/
theorem initExpA_pos {g : ℝ} (hg : g < 1) : 0 < initExpA g := by
  rw [initExpA]
  linarith only [hg]

/-- The maximal history exponent is strictly above the growth exponent
whenever that exponent is below one. -/
theorem lt_initExpRhoMax (d : ℕ) {g : ℝ} (hg : g < 1) :
    g < initExpRhoMax d g := by
  have hQ : (0 : ℝ) < (initExpQ d g : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_initExpQ d hg)
  have hnum : (0 : ℝ) < (d : ℝ) + initExpA g :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg d) (initExpA_pos hg)
  rw [initExpRhoMax]
  exact lt_add_of_pos_right g (div_pos hnum hQ)

end

end Homogenization.HighContrast.InitializationExponents
