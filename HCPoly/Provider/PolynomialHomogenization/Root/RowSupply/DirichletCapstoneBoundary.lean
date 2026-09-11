/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.CdualConditionalTerminalProducer
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.FixedParentResponsePriceAlgebra
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredObservationToPhysicalFluxRate

/-!
# Dirichlet capstone boundary

The terminal response estimate consumes a physical coefficient-energy price.
This file names that premise at the exact selected gauge-domain witness and
records its direct consumption by the conditional terminal theorem.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical coefficient-energy estimate required by RATE-AGG at one
selected gauge-domain witness. -/
def GaugePhysicalEnergyPriceAtWitness
    (U : Set (Vec d)) (aPhysical : CoeffField d) (u : H1Function U)
    (Kenergy : ℝ) (boundaryEnergy : ℝ≥0∞) : Prop :=
  0 ≤ Kenergy ∧
    eVolumeAverage U (fun z ↦
        ENNReal.ofReal (coefficientEnergyDensity aPhysical u.grad z)) ≤
      ENNReal.ofReal Kenergy * boundaryEnergy

end

end RowSupply
end HighContrast
end Homogenization
