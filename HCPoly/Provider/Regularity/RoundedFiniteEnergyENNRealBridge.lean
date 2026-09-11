/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CommonScaleRoundedOneStepAffineExcess
import HCPoly.Provider.Regularity.CorrectorWeightedGradientBridge
import HCPoly.Provider.Regularity.FiniteCubeEnergyRestriction
import HCPoly.Provider.Regularity.FiniteSequenceBounds
import HCPoly.Provider.Regularity.RoundedFiniteEnergyAnalyticBounds
import HCPoly.Provider.Regularity.SmallTailIteration

/-!
# ENNReal realization of the finite centered energy row

The Step-4 recurrence is real-valued, while the root weighted norm is
`ENNReal`-valued.  This file identifies the exact cube restrictions and lifts
the finite inequality without changing either carrier.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The weighted norm on an inner centered cube is exactly the `ENNReal`
realization of the finite centered energy row. -/
theorem weightedGradNorm_eq_ofReal_finiteCenteredCubeSolutionEnergy
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (h : ℤ) (hhm : h ≤ m) :
    weightedGradNorm (a.coeffOn (originCube d h)).toCoeffField
        (openCubeSet (originCube d h)) u.toH1.grad =
      ENNReal.ofReal (finiteCenteredCubeSolutionEnergy a m u h) := by
  let uH := finiteCubeSolutionRestriction a hhm u
  calc
    weightedGradNorm (a.coeffOn (originCube d h)).toCoeffField
        (openCubeSet (originCube d h)) u.toH1.grad =
        weightedGradNorm (a.coeffOn (originCube d h)).toCoeffField
          (openCubeSet (originCube d h)) uH.toH1.grad := by rfl
    _ = ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube (originCube d h) a uH.toH1) :=
      weightedGradNorm_eq_ofReal_h1EnergyNormOnCube
        (originCube d h) a uH.toH1
    _ = ENNReal.ofReal (finiteCenteredCubeSolutionEnergy a m u h) := by
      rw [finiteCenteredCubeSolutionEnergy_eq_of_le a m u h hhm]

end

end HighContrast
end Homogenization
