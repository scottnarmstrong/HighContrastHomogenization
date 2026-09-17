import HCPoly.Entry.Annealed.AdaptedIntegrability
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# Coarse-block integrability on every aligned cell

The terminal-optimizer replacement row averages the subcell responses over the aligned
cells of a fixed generation.  This module records that an aligned cell of the response grid
is the adapted translate at its own centre, and transports the standing stationary-law
integrability of the adapted coarse block to every such aligned cell.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- An aligned cell of the response grid is the adapted translate at its own centre. -/
theorem adaptedCellAtCenter_eq_adaptedCellTranslate {d : ℕ} [NeZero d] (q : Mat d) (j : ℤ)
    (w : Fin d → ℤ) :
    adaptedCellAtCenter q j w
      = HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j w) := rfl

/-- **Coarse-block integrability on every aligned cell of the response grid.** -/
theorem hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ) :
    HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w) := by
  rw [adaptedCellAtCenter_eq_adaptedCellTranslate]
  exact Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ Kg Src hstat hdag
    jStar hjStar (explicitCanonicalMetric F) hm j (adaptedCellCenter (respGrid jStar F) j w)

end

end Homogenization.HighContrast.Multiscale
