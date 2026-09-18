/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.CenteredResponseAbsolute
import HCPoly.Provider.Response.ConstantSkewAdjoint

/-!
# Compact pre-Young insertion at the Schur loads

The two carried compact estimates are specialized to the independently
centered primal and adjoint responses and discharged by the calibrated
defect, energy, hatted-row, and weak bounds.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory Set

open scoped ENNReal Matrix

noncomputable section

/-- The skew coordinate of a Schur block is an admissible profile gauge. -/
theorem is_skew_mat_response_skew {d : ℕ} (K : Mat d) :
    IsSkewMat (responseSkew K) := by
  rw [responseSkew, IsSkewMat, ← conjTranspose_eq_matTranspose,
    Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  rw [show Kᴴ - K = -(K - Kᴴ) by abel, smul_neg]

end

end Homogenization.HighContrast.Response
