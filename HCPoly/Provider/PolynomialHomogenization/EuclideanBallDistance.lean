/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.EuclideanAmbient

/-!
# Euclidean balls in distance form
-/

namespace Homogenization
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- Membership in `euclideanBallAt` is equivalently a strict Euclidean
distance bound when the radius is positive. -/
theorem mem_euclideanBallAt_iff_euclideanDist_lt
    {c x : Vec d} {r : ℝ} (hr : 0 < r) :
    x ∈ euclideanBallAt c r ↔ euclideanDist x c < r := by
  rw [mem_euclideanBallAt_iff, ← euclideanDist_sq]
  constructor
  · intro h
    nlinarith only [h, euclideanDist_nonneg x c, hr]
  · intro h
    nlinarith only [h, euclideanDist_nonneg x c, hr]

end

end HighContrast
end Homogenization
