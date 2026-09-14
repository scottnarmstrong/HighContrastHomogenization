/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge

/-!
# Identity-coefficient reduction of a constant-matrix dual problem

The constant-matrix dual equation can be read as an identity-coefficient
Dirichlet problem after moving the coefficient defect to the datum.  This is
the exact algebraic reduction needed before a small matrix perturbation can be
combined with the identity-coefficient positive Besov estimate.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A fixed matrix preserves vector-valued `L²` membership. -/
theorem memVectorL2_constMatrix_mul (A : Mat d) {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x ↦ matVecMul A (f x)) := by
  let L : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  have hL : ∀ x, L x = matVecMul A x := fun x ↦ rfl
  refine MemLp.of_le_mul (c := ‖L‖) hf ?_ ?_
  · have h := L.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable
    simpa only [hL] using h
  · filter_upwards [] with x
    have h := L.le_opNorm (f x)
    simpa only [hL] using h

end

end HighContrast
end Homogenization
