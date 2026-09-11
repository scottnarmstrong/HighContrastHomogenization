/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexBoundaryDistance

/-!
# Monotonicity of boundary distance

Enlarging a domain can only increase distance to its complement.
-/

namespace Homogenization
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- Boundary distance is monotone with respect to inclusion of domains. -/
theorem euclideanBoundaryDistance_mono {V U : Set (Vec d)}
    (hVU : V ⊆ U) (hUcompl : Uᶜ.Nonempty) (x : Vec d) :
    euclideanBoundaryDistance V x ≤ euclideanBoundaryDistance U x := by
  unfold euclideanBoundaryDistance
  apply Metric.infDist_le_infDist_of_subset
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, fun hyU => hy (hVU hyU), rfl⟩
  · obtain ⟨y, hy⟩ := hUcompl
    exact ⟨HilbertVec.ofVec y, ⟨y, hy, rfl⟩⟩

end

end HighContrast
end Homogenization
