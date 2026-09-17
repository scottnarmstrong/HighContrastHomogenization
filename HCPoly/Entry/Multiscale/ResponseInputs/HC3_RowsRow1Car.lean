import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsRow1Obl
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsDeficitInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyFam
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsSubcellMeas

/-!
# The terminal-optimizer replacement row with no sample-side residue

The terminal-optimizer replacement row of `p.response.transfer` — the first error row of
`e.response.cutoff.estimate` — was stated on the response carriers with three sample-side
integrability hypotheses left open: the subcell deficits, the subcell energies, and the
cutoff-weighted terminal energy.  All three follow from the data the row already carries, so the
row holds with no sample-side residue beyond the measurability of the subcell energies.

The two declarations below restate `cutoffEnergyDefectRowMinus_of_carriers` and its adjoint twin
with those three integrability hypotheses removed, discharging them from the subcell-energy
measurability as an almost-everywhere strong measurability.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The first error row of `p.response.transfer` on the response carriers with no sample-side
residue, minus sign.**  Under the hypotheses of the carrier bound for the terminal optimizer `uM`
of the recentred coefficient `a_- = a - g`, only the subcell-energy measurability
(`hmeasE`) is assumed: the integrability of the subcell deficits, of the subcell energies and of
the cutoff-weighted terminal energy follows from it, together with the annealed data already
carried.  The conclusion is the named obligation
`CutoffEnergyDefectRowMinus` at the explicit constant
`max 3 (32 d^2 responseCutoffProfileConst)`. -/
theorem cutoffEnergyDefectRowMinus_of_carriers_of_measurable {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, Measurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) :
    CutoffEnergyDefectRowMinus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uM := by
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    fun w hw => (hmeasE w hw).aestronglyMeasurable
  have hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P := by
    have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
    refine (measurable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e uM
      hmax (eta := fun x => φ x - 1) ?_ ?_).aestronglyMeasurable
    · exact (hφm.sub measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        linarith only [abs_isResponseCutoff_sub_one hφ x])
  have hD : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P :=
    integrable_subcellDeficit_respCoeffMinus P jStar hjStar F hm H s t ht hjs e uM hmax
      (hblk s) hJt hmeasEae
  have hE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm H s t ht e
      uM hmax hJt hmeasEae
  have hW : MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P :=
    integrable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e φ hφ uM
      hmax hJt hmeasW
  exact cutoffEnergyDefectRowMinus_of_carriers P hstat jStar hjStar F hm H s t ht hjs e φ hφ uM
    hmax hblk hJt hJs hD hE hW

/-- **The first error row of `p.response.transfer` on the response carriers with no sample-side
residue, plus sign.**  This is the adjoint twin of
`cutoffEnergyDefectRowMinus_of_carriers_of_measurable`: the coefficient family `a_+ = aᵀ + g`, the
dual load `q^+` and the terminal optimizer family `uP` replace their minus-sign counterparts, and
the subcell-energy measurability discharges the same three sample-side integrabilities.  The
conclusion is the named obligation `CutoffEnergyDefectRowPlus` at the explicit constant
`max 3 (32 d^2 responseCutoffProfileConst)`. -/
theorem cutoffEnergyDefectRowPlus_of_carriers_of_measurable {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, Measurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) :
    CutoffEnergyDefectRowPlus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uP := by
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    fun w hw => (hmeasE w hw).aestronglyMeasurable
  have hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P := by
    have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
    refine (measurable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e uP
      hmax (eta := fun x => φ x - 1) ?_ ?_).aestronglyMeasurable
    · exact (hφm.sub measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        linarith only [abs_isResponseCutoff_sub_one hφ x])
  have hD : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P :=
    integrable_subcellDeficit_respCoeffPlus P jStar hjStar F hm H s t ht hjs e uP hmax
      (hblk s) hJt hmeasEae
  have hE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm H s t ht e
      uP hmax hJt hmeasEae
  have hW : MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P :=
    integrable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e φ hφ uP
      hmax hJt hmeasW
  exact cutoffEnergyDefectRowPlus_of_carriers P hstat jStar hjStar F hm H s t ht hjs e φ hφ uP
    hmax hblk hJt hJs hD hE hW

/-- **The terminal-optimizer replacement row of `p.response.transfer` on the carriers, minus
sign.**  The row holds with no sample-side hypothesis beyond the annealed data it already carries:
the measurability of the subcell energies is supplied by the canonical selection, and the three
integrabilities of the subcell deficits, of the subcell energies and of the cutoff-weighted
terminal energy follow by domination. -/
theorem cutoffEnergyDefectRowMinus_of_carriers_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    CutoffEnergyDefectRowMinus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uM :=
  cutoffEnergyDefectRowMinus_of_carriers_of_measurable P hstat jStar hjStar F hm H s t ht hjs e φ
    hφ uM hmax hblk hJt hJs
    (fun w hw => measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
      H s t ht e uM hmax w hw)

/-- **The terminal-optimizer replacement row of `p.response.transfer` on the carriers, plus
sign.**  The adjoint twin of `cutoffEnergyDefectRowMinus_of_carriers_clean`. -/
theorem cutoffEnergyDefectRowPlus_of_carriers_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    CutoffEnergyDefectRowPlus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uP :=
  cutoffEnergyDefectRowPlus_of_carriers_of_measurable P hstat jStar hjStar F hm H s t ht hjs e φ
    hφ uP hmax hblk hJt hJs
    (fun w hw => measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
      H s t ht e uP hmax w hw)

end

end Homogenization.HighContrast.Multiscale
