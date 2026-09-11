/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
/- Dirichlet right-hand-side estimates on ruled Whitney cells. -/

import HCPoly.Provider.PolynomialHomogenization.RuledWhitneyRowCauchySchwarz
import Homogenization.Book.Ch03.Theorems.CoarsePoincareRHS
import Homogenization.Book.Ch03.Theorems.CoarseFluxResponseRHS
import Homogenization.Book.Ch03.Theorems.EnergyRHS.Theory

namespace Homogenization
namespace HighContrast
open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The triadic cube represented by one index of a convex Whitney system. -/
def whitneyCellCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : TriadicCube d :=
  translateCube (system.index i) (originCube d (system.scale i))

@[simp] theorem openCubeSet_whitneyCellCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    openCubeSet (whitneyCellCube system i) = system.cell i := rfl

private theorem normalizedWhitneyRowEnergy_mono
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {X Y : system.CellIndex → ℝ≥0∞}
    (hXY : ∀ i, X i ≤ Y i) :
    normalizedWhitneyRowEnergy system X ≤
      normalizedWhitneyRowEnergy system Y := by
  unfold normalizedWhitneyRowEnergy rawWhitneyRowEnergy
  apply mul_le_mul_right
  exact ENNReal.tsum_le_tsum fun i =>
    mul_le_mul_right (hXY i) (volume (system.cell i))

end

end HighContrast
end Homogenization
