/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.ObservationCoefficientTransport
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import HCPoly.Provider.Regularity.FiniteCubeSolutionRestriction
import Homogenization.Book.Ch03.Definitions
import Homogenization.Geometry.BoundaryLayer
import Homogenization.Geometry.CubeMetric
import Homogenization.Sobolev.H1.LocalizedZeroTrace
import Mathlib.Order.Filter.CountableInter
import HCPoly.Provider.PolynomialHomogenization.RuledWhitneyPhysicalDualRHSRow
import HCPoly.Provider.Regularity.EnlargedMarginDatumRegularity

/-!
# Observation-cube comparison pricing on ruled Whitney cells

Each ruled cell is viewed from the center of its concentric threefold
interior buffer.  The comparison problem is solved on the resulting
origin-centered observation cube.  Its priced fields are then evaluated on
the translated copy of the ruled cell, which is covered by the canonical
depth-one child cores.
-/

namespace Homogenization
namespace HighContrast
open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical center used to translate one ruled cell to the origin. -/
def ruledObservationCenter
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : Vec d :=
  standardCellCenter (system.scale i) (system.index i)

/-- The origin-centered observation cube is one generation larger than the
ruled cell. -/
def ruledObservationCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : TriadicCube d :=
  originCube d (system.scale i + 1)

/-- The translated observation cube lies in the enlarged ruled interior
buffer. -/
theorem translateSet_observationCube_subset_interiorBuffer
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    translateSet (ruledObservationCenter system i)
        (openCubeSet (ruledObservationCube system i)) ⊆
      system.interiorBuffer i := by
  intro x hx
  rw [interiorBuffer_eq_translateSet_ambientCube]
  apply mem_translateSet_iff_sub_mem.mpr
  have hx' := mem_translateSet_iff_sub_mem.mp hx
  have hxObs : x - enlargedMarginObservationCenter system i ∈
      openCubeSet (originCube d (system.scale i + 1)) := by
    simpa [ruledObservationCenter, ruledObservationCube,
      enlargedMarginObservationCenter,
      enlargedMarginAmbientCube] using hx'
  exact openCubeSet_originCube_subset_of_le
    (show system.scale i + 1 ≤ system.scale i + 2 by omega) hxObs

end

end HighContrast
end Homogenization
