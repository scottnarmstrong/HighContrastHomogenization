/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
import HCPoly.Provider.PolynomialHomogenization.RuledObservationComparisonPricing
import HCPoly.Provider.PolynomialHomogenization.RuledPairingAggregation
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic
import Homogenization.Deterministic.WeakNormInterfacesComponentwise

/-!
# Buffered comparison realizations on ruled Whitney cells

The constant-coefficient comparison datum is restricted to each inward
physical buffer and translated to its origin-centered observation cube.  A
single observation Dirichlet family supplies the prescribed trace, the
physical-cell comparison fields, and the mixed Caccioppoli row.
-/

namespace Homogenization
namespace HighContrast
open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical flux defect on one ruled cell. -/
def ruledPhysicalFluxDefectOnCell
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (aPhysical : CoeffField d)
    (a0 : system.CellIndex → ConstantCoeffMatrix d)
    (u : H1Function U) (i : system.CellIndex) (x : Vec d) : Vec d :=
  matVecMul (aPhysical x - (a0 i).matrix) (u.grad x)

end

end HighContrast
end Homogenization
