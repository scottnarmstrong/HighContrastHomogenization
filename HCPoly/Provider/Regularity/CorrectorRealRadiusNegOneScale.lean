/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CorrectorRealRadiusNegOne
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Running-scale normalization for centered-cube negative-one norms

This module compares inverse-side-length normalizations on a centered cube of
real side length and its canonical enclosing triadic origin cube.  The only
analytic input is the quotient-safe centered-cube restriction estimate.
-/

namespace Homogenization
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- The inverse-side-length normalized negative-one norm on a centered cube
of real side length. -/
noncomputable def realRadiusScaledNegOneNorm {d : ℕ} (R : ℝ)
    (F : HilbertVectorL2 (centeredOpenCube d R)) : ℝ≥0∞ :=
  ENNReal.ofReal R⁻¹ * localNegOneNorm (centeredOpenCube d R) F

/-- The inverse-side-length normalized negative-one norm on an origin cube
of integer triadic generation. -/
noncomputable def triadicScaledNegOneNorm {d : ℕ} (n : ℤ)
    (F : HilbertVectorL2 (openCubeSet (originCube d n))) : ℝ≥0∞ :=
  ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
    localNegOneNorm (openCubeSet (originCube d n)) F

end

end HighContrast
end Homogenization
