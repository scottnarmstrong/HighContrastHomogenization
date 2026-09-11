/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexFractionalChainMeanTelescope
import HCPoly.Analytic.NormComparison

/-!
# Convergence of shrinking convex-chain ball means
-/

namespace Homogenization
namespace HighContrast

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

private theorem volume_chainBall_pos (c x : Vec d) {rho : ℝ}
    (hrho : 0 < rho) (n : ℕ) :
    0 < volume (convexFractionalChainBall c x rho n) := by
  unfold convexFractionalChainBall
  exact IsOpen.measure_pos volume
    (isOpen_euclideanBallAt _ _)
    ⟨_, center_mem_euclideanBallAt _
      (mul_pos (convexFractionalChainScale_pos n) hrho)⟩

private theorem volume_chainBall_ne_top (c x : Vec d) {rho : ℝ}
    (hrho : 0 < rho) (n : ℕ) :
    volume (convexFractionalChainBall c x rho n) ≠ ⊤ := by
  exact (isOpenBoundedConvexDomain_euclideanBallAt _
    (mul_pos (convexFractionalChainScale_pos n) hrho)).volume_lt_top.ne

end

end HighContrast
end Homogenization
