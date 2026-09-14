/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.AffineH10
import HCPoly.Analytic.AffineNegSobolevNorm
import HCPoly.Analytic.H1a0ToH10
import HCPoly.Provider.Initialization.IdentityGrid
import HCPoly.Provider.PolynomialHomogenization.AffineCoeffFamily
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootCoefficient
import HCPoly.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
import HCPoly.Provider.PolynomialHomogenization.RuledLocalizationAssembly
import HCPoly.Provider.PolynomialHomogenization.ScalarCubeFluxComparison
import HCPoly.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
import HCPoly.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderRateBearingEvent
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra
import HCPoly.Provider.PolynomialHomogenization.Root.Localization.LocalizationSupply
import HCPoly.Provider.Recurrence.AdaptedCellDomain
import HCPoly.Provider.Regularity.AffineTransfer
import HCPoly.Provider.Regularity.CorrectorGlobalEquation
import HCPoly.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
import Homogenization.Book.Ch01.Theorems.CutoffProduct
import Homogenization.Book.Ch02.Theorems.HomogenizationError.Basic
import Homogenization.Deterministic.WeakNormInterfaces.AECongruence
import Homogenization.Sobolev.Fractional.DefinitionsAPI

/-!
# The centered one-step indicator extension

The child test is extended by zero to its centered parent and multiplied by
the parent-to-child volume ratio.  This module proves the exact pairing
identity and the local square-integrability part of the parent test carrier.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {s : ℝ}

/-- The centered scale-`m` cube is the middle child of the centered
scale-`m+1` cube. -/
theorem originCube_mem_childCubes_succ (d : ℕ) (m : ℤ) :
    originCube d m ∈ childCubes (originCube d (m + 1)) := by
  simpa [originCube] using! middleChild_mem_childCubes (originCube d (m + 1))

end

end RowSupply
end HighContrast
end Homogenization
