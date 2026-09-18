/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.FiniteLipschitzCoreDefinitions
import HCPoly.Provider.Regularity.CorrectorNormalizedL2Bridge
import HCPoly.Provider.Regularity.AffineTransfer
import HCPoly.Provider.Regularity.RoundedReferenceConstantMatrix
import HCPoly.Provider.Response.AffineResponseGeometry
import HCPoly.Provider.Selection.EnclosureGeometry
import HCPoly.Provider.Transport.WhitneySquareWeights
import HCPoly.Provider.Regularity.CubeVolume
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
import Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.CoordinateStandard
import Homogenization.Sobolev.Fractional.ContinuousInterpolation.OverlapCoordinateBridge
import Homogenization.Sobolev.Fractional.ExactOverlapEuclideanComparison
import HCPoly.Provider.Regularity.CenteredCubeEuclideanHsFullNormConstantMatrix
import HCPoly.Provider.Regularity.CommonQuantitativeAffineScale
import HCPoly.Provider.Regularity.RoundedOuterSpatialResponsePowerTail
import HCPoly.Provider.Regularity.RoundedPhysicalDirichletEuclideanHs
import Homogenization.Besov.Negative.ExactAggregationBridge
import Homogenization.Besov.PositiveOverlapBridge
import Homogenization.Book.Ch01.Theorems.NegativeBesovLocalize
import Homogenization.Sobolev.Fractional.ExactOverlapEuclideanFullComparison
import HCPoly.Provider.Regularity.RoundedCenteredCoeffFamily
import HCPoly.Provider.Regularity.RoundedHarmonicReplacement
import Homogenization.Book.Ch02.Theorems.HomogenizationError.AEEq
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors
import Homogenization.Deterministic.CoarseFluxResponse.Response
import Homogenization.Deterministic.CoarseFluxResponse.RHSCorrections
import Homogenization.Deterministic.CoarsePoincare.QTwo
import HCPoly.Provider.Regularity.CorrectorWeightedGradientBridge
import HCPoly.Provider.Regularity.FiniteCubeEnergyRestriction
import HCPoly.Provider.Regularity.FiniteSequenceBounds
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
