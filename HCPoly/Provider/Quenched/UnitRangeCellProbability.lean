/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.UnitRangeBlockReassembly
import HCPoly.Provider.Quenched.UnitRangeCellRenormalization
import HCPoly.Provider.Quenched.UnitRangeInnerCells
import HCPoly.Provider.Quenched.UnitRangeNormalizedCutoff

/-!
# The probabilistic normalized cell estimate

The unit-range concentration bound is applied at a shifted parameter so that
the finite block-entry union bound is absorbed into the Gaussian gauge.
-/

namespace Homogenization
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The dimensional parameter shift absorbing whole-block reassembly. -/
def unitRangeRenormShift (d : ℕ) : ℝ :=
  Real.log (4 * (d : ℝ) ^ 2 + 1) / (2 * frGaugeConst d)

theorem unitRangeRenormShift_nonneg (d : ℕ) : 0 ≤ unitRangeRenormShift d := by
  refine div_nonneg (Real.log_nonneg ?_) ?_
  · nlinarith only [sq_nonneg ((d : ℝ))]
  · exact (mul_nonneg (by norm_num) (frGaugeConst_pos d).le)

end

end Quenched
end HighContrast
end Homogenization
