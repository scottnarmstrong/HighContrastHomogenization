/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredObservationToPhysicalFluxRate

/-!
# Scheduled-rate extraction from the squared flux row

The squared Whitney-row rate is converted to the terminal one-half power.  All
finite deterministic factors are retained in one explicit real constant.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- CapObs-free terminal rate on the module-50 response-window witness. -/
def RowConvertedFluxScheduledRateAtWitness
    (d : ℕ) [NeZero d] (C₀ : ℝ → ℝ → ℝ → ℝ)
    (_g kappaRate Cdual : ℝ)
    (capFlux hardyConstant boundaryEnergy : ℝ≥0∞)
    (s rho Rad epsilon Xval outputFactor : ℝ) : Prop :=
  capFlux ≠ ⊤ ∧
    ENNReal.ofReal outputFactor *
        (ENNReal.ofReal Cdual *
          ruledScheduledTwoRowCap d hardyConstant capFlux) ≤
      ENNReal.ofReal (C₀ s rho Rad * (epsilon * Xval) ^ kappaRate) *
        boundaryEnergy ^ (1 / 2 : ℝ)

end

end RowSupply
end HighContrast
end Homogenization
