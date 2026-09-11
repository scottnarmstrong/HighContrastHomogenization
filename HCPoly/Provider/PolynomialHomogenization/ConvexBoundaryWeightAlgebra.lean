/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexBoundaryWeightMoment

/-!
# Algebra of negative boundary-distance weights
-/

namespace Homogenization
namespace HighContrast

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Negative boundary-distance weights multiply by adding their orders at
points of positive boundary distance. -/
theorem euclideanBoundaryWeight_mul
    {U : Set (Vec d)} {x : Vec d} (hx : 0 < euclideanBoundaryDistance U x)
    (p q : ℝ) :
    euclideanBoundaryWeight U p x * euclideanBoundaryWeight U q x =
      euclideanBoundaryWeight U (p + q) x := by
  unfold euclideanBoundaryWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),
    ← Real.rpow_add hx]
  congr 2
  ring

/-- Multiplying an order-`s` boundary weight by `delta^(s-a)` leaves the
order-`a` boundary weight. -/
theorem euclideanBoundaryWeight_mul_ofReal_rpow_sub
    {U : Set (Vec d)} {x : Vec d} (hx : 0 < euclideanBoundaryDistance U x)
    (s a : ℝ) :
    euclideanBoundaryWeight U s x *
        ENNReal.ofReal (euclideanBoundaryDistance U x ^ (s - a)) =
      euclideanBoundaryWeight U a x := by
  unfold euclideanBoundaryWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),
    ← Real.rpow_add hx]
  congr 2
  ring

end

end HighContrast
end Homogenization
