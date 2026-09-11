/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.QuantitativeGoodTail

/-!
# Folding a constant into the activation length

The reference text's homogenization estimate is stated with a law-free
amplitude and a homogenization length that carries the aspect ratio of the
homogenized matrix, rather than with an amplitude that carries it.  The passage
from the first form to the second is a redefinition of the length: a bounded
constant multiplying a quantitative power tail is absorbed by enlarging the
activation length by the corresponding root, after which the amplitude is
law-free and the whole dependence sits inside the ratio the tail is stated
against.

This file records that move for `ScalarIdentityPowerTail`, together with the
transport of a folded tail to any larger activation length, which is the form
the response chain consumes.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- A constant at least one has all its positive real powers at least one. -/
theorem one_le_rpow_of_one_le {C z : ℝ} (hC : 1 ≤ C) (hz : 0 ≤ z) :
    (1 : ℝ) ≤ C ^ z := by
  calc (1 : ℝ) = (1 : ℝ) ^ z := (Real.one_rpow z).symm
    _ ≤ C ^ z := Real.rpow_le_rpow zero_le_one hC hz

end

end RowSupply
end HighContrast
end Homogenization
