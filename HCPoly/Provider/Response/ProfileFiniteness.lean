/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowSkewCarriers
import HCPoly.Provider.Response.ProfileWeakCarriers

/-!
# Finiteness bridges for terminal response profiles

Fail-closed extended nonnegative profile quantities are converted to real
estimates only after an explicit finite upper bound has been established.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- An extended nonnegative quantity below `ofReal C` has the exact real
upper bound when `C` is nonnegative. -/
theorem toReal_le_of_le_ofReal {x : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (h : x ≤ ENNReal.ofReal C) : x.toReal ≤ C := by
  have htop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hC] at hreal

end

end Homogenization.HighContrast.Response
