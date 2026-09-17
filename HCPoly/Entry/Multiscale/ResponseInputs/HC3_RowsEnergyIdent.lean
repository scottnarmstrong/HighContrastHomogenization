import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cmp

/-!
# The terminal cell energy of the optimizer on the response carriers

At a response maximizer the variation energy of the optimizer is exactly twice the response, so the
volume average of its energy density over the terminal cell is `2 J_t^∓`.  Exact partition averaging
then spreads that identity over the aligned subcells of the coarse scale, and the energy density is
nonnegative almost everywhere on every such subcell because the coefficient has an elliptic
representative on the terminal cell.  These are the pathwise facts from which the sample-side
integrability of the subcell energies is obtained by domination, and they are the first error row of
`p.response.transfer` at the level of the carriers.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Integrability of the variation energy of a harmonic field for a coefficient that agrees almost
everywhere with a pointwise elliptic representative. -/
private theorem integrableOn_energy_of_aeRep {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U b)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hae : a =ᵐ[volumeMeasureOn U] b)
    (u : AHarmonicFunction a U) :
    MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) U := by
  have hdata : ResponseLinearIntegrabilityData U b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hE : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand b (aHarmonicFunctionOfAEEqCoeff hae u)) U :=
    hdata.energy (aHarmonicFunctionOfAEEqCoeff hae u)
  refine hE.congr ?_
  filter_upwards [hae] with x hx
  simp only [scalarVariationEnergyIntegrand, grad_aHarmonicFunctionOfAEEqCoeff]
  rw [hx]

/-- Nonnegativity of the variation energy average on a subset, for a coefficient that agrees almost
everywhere with a pointwise elliptic representative on the enclosing set. -/
private theorem volumeAverage_energy_nonneg_of_aeRep {d : ℕ} {U V : Set (Vec d)}
    {a b : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U b)
    (hVU : V ⊆ U) (hV : MeasurableSet V) (hae : a =ᵐ[volumeMeasureOn U] b)
    (u : AHarmonicFunction a U) :
    0 ≤ volumeAverage V (scalarVariationEnergyIntegrand a u) := by
  have hnn : 0 ≤ volumeAverage V
      (scalarVariationEnergyIntegrand b (aHarmonicFunctionOfAEEqCoeff hae u)) := by
    refine volumeAverage_nonneg_of_nonneg_on hV ?_
    intro x hx
    exact scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U b hEll
      (aHarmonicFunctionOfAEEqCoeff hae u) x (hVU hx)
  rwa [volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae u] at hnn

/-- The energy identity at a response maximizer, for a coefficient that agrees almost everywhere
with a pointwise elliptic representative: the terminal energy average is twice the response. -/
private theorem volumeAverage_energy_eq_two_respJ_of_aeRep {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U b)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hae : a =ᵐ[volumeMeasureOn U] b)
    (p r : Vec d) (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p r a u) :
    volumeAverage U (scalarVariationEnergyIntegrand a u) = 2 * ResponseJ U p r a := by
  have hdata : ResponseLinearIntegrabilityData U b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hmaxb : IsResponseMaximizer U p r b (aHarmonicFunctionOfAEEqCoeff hae u) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have henergy : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand b (aHarmonicFunctionOfAEEqCoeff hae u)) U :=
    hdata.energy (aHarmonicFunctionOfAEEqCoeff hae u)
  have hresp : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U b p r (aHarmonicFunctionOfAEEqCoeff hae u)) U :=
    hdata.response p r (aHarmonicFunctionOfAEEqCoeff hae u)
  have hlin : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand U b p r (aHarmonicFunctionOfAEEqCoeff hae u)
        (aHarmonicFunctionOfAEEqCoeff hae u)) U :=
    hdata.firstVariation p r (aHarmonicFunctionOfAEEqCoeff hae u)
      (aHarmonicFunctionOfAEEqCoeff hae u)
  have hident : ResponseJ U p r b
      = (1 / 2 : ℝ) * volumeAverage U
          (scalarVariationEnergyIntegrand b (aHarmonicFunctionOfAEEqCoeff hae u)) :=
    responseJ_energy_of_isResponseMaximizer U b p r (aHarmonicFunctionOfAEEqCoeff hae u) hmaxb
      (hdata.weakFlux (aHarmonicFunctionOfAEEqCoeff hae u)) hresp hlin henergy
  have hJ : ResponseJ U p r a = ResponseJ U p r b := responseJ_congr_of_ae_eq hae p r
  have hE : volumeAverage U
        (scalarVariationEnergyIntegrand b (aHarmonicFunctionOfAEEqCoeff hae u))
      = volumeAverage U (scalarVariationEnergyIntegrand a u) :=
    volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff (fun _ hx => hx)
      hae u
  rw [hJ, hident, hE]
  ring

/-- **Integrability of the terminal optimizer energy, minus sign.**  On the terminal cell the
variation energy density of a terminal maximizer for `a_- = a - g` is integrable; the coefficient is
elliptic only almost everywhere, so the fact is transported from an elliptic representative. -/
theorem integrableOn_energy_respCell_respCoeffMinus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  exact integrableOn_energy_of_aeRep hEll hae (uM a)

/-- **The terminal energy identity, minus sign.**  At a terminal maximizer for `a_- = a - g` the
volume average of the optimizer energy density over the terminal cell is twice the terminal
response, the exact energy identity behind the first error row of `p.response.transfer`. -/
theorem volumeAverage_energy_respCell_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) (a : CoeffSpace d) :
    volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hcore := volumeAverage_energy_eq_two_respJ_of_aeRep (U := respCell jStar F t) hEll hae
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a) (hmax a)
  simpa only [respJ, respCell] using hcore

/-- **Nonnegativity of the subcell energy, minus sign.**  On every aligned subcell of the coarse
scale the average of the terminal optimizer energy density is nonnegative, because the terminal
coefficient is elliptic almost everywhere there. -/
theorem zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  exact volumeAverage_energy_nonneg_of_aeRep (U := respCell jStar F t) hEll hVU hV hae (uM a)

/-- **Exact partition averaging of the terminal energy, minus sign.**  The normalized sum over the
aligned subcells of the coarse scale of the optimizer energy averages equals the terminal energy
average, since those subcells partition the terminal cell up to a null set. -/
theorem avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      = volumeAverage (respCell jStar F t)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hf : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    simpa only [respCell] using
      integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
  have h := avsum_volumeAverage_eq (respGrid jStar F) hq t H hf
  rw [show t - (H : ℤ) = s by omega] at h
  simpa only [respCell] using h

/-- **Integrability of the terminal optimizer energy, plus sign.**  The twin of the minus statement
for `a_+ = aᵗ + g`. -/
theorem integrableOn_energy_respCell_respCoeffPlus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  exact integrableOn_energy_of_aeRep hEll hae (uP a)

/-- **The terminal energy identity, plus sign.**  The twin of the minus identity for
`a_+ = aᵗ + g`. -/
theorem volumeAverage_energy_respCell_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) (a : CoeffSpace d) :
    volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hcore := volumeAverage_energy_eq_two_respJ_of_aeRep (U := respCell jStar F t) hEll hae
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a) (hmax a)
  simpa only [respJ, respCell] using hcore

/-- **Nonnegativity of the subcell energy, plus sign.**  The twin of the minus statement for
`a_+ = aᵗ + g`. -/
theorem zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  exact volumeAverage_energy_nonneg_of_aeRep (U := respCell jStar F t) hEll hVU hV hae (uP a)

/-- **Exact partition averaging of the terminal energy, plus sign.**  The twin of the minus
statement for `a_+ = aᵗ + g`. -/
theorem avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      = volumeAverage (respCell jStar F t)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hf : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    simpa only [respCell] using
      integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
  have h := avsum_volumeAverage_eq (respGrid jStar F) hq t H hf
  rw [show t - (H : ℤ) = s by omega] at h
  simpa only [respCell] using h

end

end Homogenization.HighContrast.Multiscale
