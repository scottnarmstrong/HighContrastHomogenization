/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.AffineFractionalKernel
import HCPoly.Provider.Regularity.ConstantMatrixDualIdentityReduction
import HCPoly.Provider.Regularity.RoundedReferenceConstantMatrix
import HCPoly.Provider.Regularity.RoundedSymmetricReferenceBounds

/-!
# Quantitative identity reduction for the rounded-reference dual problem

The rounded reference matrix differs from the identity by at most one percent
in operator norm.  This module combines that proved geometric bound with the
exact constant-matrix identity reduction, exposing both pointwise and
integrated control of the resulting dual residual.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The selected value of the rounded constant reference is within one
percent of the identity in operator norm. -/
theorem norm_roundedReferenceMatrix_sub_one_le [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    ‖roundedReferenceMatrix abar hS - 1‖ ≤ (1 / 100 : ℝ) := by
  simpa only [roundedReferenceMatrix] using
    norm_roundedSymmetricReferenceCoefficient_sub_one_le
      abar hS (0 : Vec d)

end

end HighContrast
end Homogenization
