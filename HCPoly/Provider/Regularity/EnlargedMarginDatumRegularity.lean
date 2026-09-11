/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.RuledTriadicWhitneyCarrier
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyEndpoint
import HCPoly.Provider.Regularity.LiouvilleCubeRestriction
import HCPoly.Provider.Regularity.AffineTransfer
import Homogenization.Book.Ch03.Definitions
import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicInteriorHessian
import Homogenization.Book.Ch03.Theorems.DualityPositivePairing
import Homogenization.Besov.Poincare.Projection
import HCPoly.Provider.Regularity.ObservationCoefficientTransport

/-!
# Observation-datum regularity from enlarged Whitney margins

The ninefold admissibility buffer places both the closure of the observation
cube and that cube itself inside the strict inner half of the next centered
triadic cube.  This supplies the geometric hypotheses of the constant-
coefficient datum regularity theorem after translating a selected cell to the
origin.
-/

namespace Homogenization
namespace HighContrast
open Book Book.Ch03 MeasureTheory Set
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The center used to view an enlarged-margin cell from the origin. -/
def enlargedMarginObservationCenter
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : Vec d :=
  standardCellCenter (system.scale i) (system.index i)

/-- The ambient cube furnished by ninefold admissibility is one scale larger
than the observation cube. -/
def enlargedMarginAmbientCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : TriadicCube d :=
  originCube d (system.scale i + 2)

/-- The enlarged admissibility buffer is the translated ambient cube. -/
theorem interiorBuffer_eq_translateSet_ambientCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    system.interiorBuffer i =
      translateSet (enlargedMarginObservationCenter system i)
        (openCubeSet (enlargedMarginAmbientCube system i)) := by
  unfold EnlargedMarginRuledTriadicWhitneySystem.interiorBuffer
    enlargedMarginWhitneyInteriorBuffer enlargedMarginObservationCenter
    enlargedMarginAmbientCube
  rw [openCubeAtScale_eq_translateSet,
    openCubeAtScale_zero_eq_openCubeSet_originCube]

end

end HighContrast
end Homogenization
