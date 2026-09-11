/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.DatumRowAggregation
import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
import Homogenization.Book.Ch03.Theorems.CoarsePoincare

/-!
# Response price for the direct gradient energy map

The coarse response controls the inverse effective ellipticity in the direct
gradient estimate.  The Whitney geometry supplies a uniform upper bound for
the parent-scale normalization.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The physical dual scale factor written as a single power. -/
theorem physicalDualBesovScaleFactor_eq_rpow
    (Q : TriadicCube d) (s : ℝ) :
    physicalDualBesovScaleFactor Q s =
      Real.rpow (3 : ℝ) (s * ((Q.scale : ℤ) : ℝ)) := by
  unfold physicalDualBesovScaleFactor
  have hneg : Real.rpow (3 : ℝ) (-(s * ((Q.scale : ℤ) : ℝ))) =
      (Real.rpow (3 : ℝ) (s * ((Q.scale : ℤ) : ℝ)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [show -s * ((Q.scale : ℤ) : ℝ) =
    -(s * ((Q.scale : ℤ) : ℝ)) by ring, hneg, inv_inv]

end

end RowSupply
end HighContrast
end Homogenization
