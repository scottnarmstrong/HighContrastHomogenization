import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsSubcellMeas

/-!
# The annealed cell energy of the terminal optimizer on a descendant cell

The oscillation half of the cutoff-mean row of `p.response.transfer` reads the cell energy of the
terminal optimizer on every descendant cell of the terminal cell.  `HC3_RowsEnergyInt` makes that
readout `P`-integrable on the aligned cells of one fixed generation, from the integrability of the
terminal energy and the measurability of `HC3_RowsSubcellMeas`; the descendant generation
`t - (H + n + 1)` is that statement at the shifted scale `s - (n + 1)` and the deeper index box,
because the terminal cell is the same cell either way.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The annealed cell energy on a descendant cell, minus sign.**  The cell energy of the terminal
optimizer on a cell of the generation `t - (H+n+1)` is `P`-integrable. -/
theorem integrable_volumeAverage_energy_descendant_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (n : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d (H + n + 1)) :
    Integrable (fun a => volumeAverage
      (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := by
  have hshift : t - ((H + n + 1 : ℕ) : ℤ) = s - ((n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  have ht' : t = (s - ((n + 1 : ℕ) : ℤ)) + ((H + n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  rw [hshift]
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
    (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uM hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F
      hm (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uM hmax w hw).aestronglyMeasurable)
    W hW

/-- **The annealed cell energy on a descendant cell, plus sign.**  The adjoint twin. -/
theorem integrable_volumeAverage_energy_descendant_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (n : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d (H + n + 1)) :
    Integrable (fun a => volumeAverage
      (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := by
  have hshift : t - ((H + n + 1 : ℕ) : ℤ) = s - ((n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  have ht' : t = (s - ((n + 1 : ℕ) : ℤ)) + ((H + n + 1 : ℕ) : ℤ) := by
    rw [ht]; push_cast; ring
  rw [hshift]
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
    (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uP hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F
      hm (H + n + 1) (s - ((n + 1 : ℕ) : ℤ)) t ht' e uP hmax w hw).aestronglyMeasurable)
    W hW

end

end Homogenization.HighContrast.Multiscale
