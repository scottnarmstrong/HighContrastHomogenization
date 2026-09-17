import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cmp

/-!
# Pathwise integrability of the weighted optimizer coordinates of the cutoff-mean split

The cutoff-mean comparison of `p.response.transfer` integrates a coordinate of the doubled
optimizer state of the terminal optimizer against a bounded weight over a measurable subset of
the terminal cell.  This module records the two pathwise integrability facts that step needs for
the recentred response coefficient `respCoeffMinus F a` and for its transposed twin
`respCoeffPlus F a`: the weighted first coordinate `η · ∇v` and the weighted second coordinate
`η · (b ∇v)`, on any measurable `V` contained in the terminal cell.

The coefficient of the carrier is elliptic only almost everywhere, so the argument runs at the
pointwise elliptic representative supplied by
`exists_elliptic_representative_respCell_respCoeffMinus` / `…Plus`, extracts the coordinate
integrabilities of the representative through `ResponseLinearIntegrabilityData`, transports them
back across the almost-everywhere equality, restricts to `V`, and multiplies by the bounded
continuous weight.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Weighted optimizer coordinates for the minus response coefficient.**  For a terminal
maximizer `uM a` of the recentred coefficient `respCoeffMinus F a` on the terminal cell, and any
measurable `V` contained in that cell, both coordinates of the doubled optimizer state weighted by
a continuous `η` are integrable on `V`: the weighted gradient coordinate `η · ∇v` and the weighted
flux coordinate `η · (b ∇v)`.  The coefficient is transported from its almost-everywhere elliptic
representative, so the statement carries no pointwise ellipticity hypothesis. -/
theorem integrableOn_weighted_optimizerField_respCell_respCoeffMinus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta) (a : CoeffSpace d) (i : Fin d) :
    MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i) V
    ∧ MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i) V := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    hconv.isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hgradC : MeasureTheory.IntegrableOn
      (fun x => (uM a).toH1.grad x i) (respCell jStar F t) := by
    have h := hdata.grad (Pi.single i 1) (aHarmonicFunctionOfAEEqCoeff hae (uM a))
    simpa [vecDot_single_left, grad_aHarmonicFunctionOfAEEqCoeff] using h
  have hfluxC : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uM a).toH1.grad x) i) (respCell jStar F t) := by
    have h := hdata.flux (Pi.single i 1) (aHarmonicFunctionOfAEEqCoeff hae (uM a))
    simpa [vecDot_single_left, grad_aHarmonicFunctionOfAEEqCoeff] using h
  have hgradV : MeasureTheory.IntegrableOn (fun x => (uM a).toH1.grad x i) V :=
    hgradC.mono_set hVU
  have hfluxV : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uM a).toH1.grad x) i) V := hfluxC.mono_set hVU
  have hfluxCoord : MeasureTheory.IntegrableOn
      (fun x => matVecMul ((respCoeffMinus F a) x) ((uM a).toH1.grad x) i) V := by
    refine hfluxV.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae.symm] with x hx
    rw [hx]
  have hK : IsCompact (closure (respCell jStar F t)) :=
    hconv.isBoundedDomain.isBounded.isCompact_closure
  have hVK : V ⊆ closure (respCell jStar F t) := fun x hx => subset_closure (hVU hx)
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hgradV hK hV hVK
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hfluxCoord hK hV hVK

/-- **Weighted optimizer coordinates for the plus response coefficient.**  The transposed twin of
`integrableOn_weighted_optimizerField_respCell_respCoeffMinus`: for a terminal maximizer `uP a` of
`respCoeffPlus F a` on the terminal cell and any measurable `V` contained in that cell, the
continuous-weight products `η · ∇v` and `η · (b ∇v)` are integrable on `V`. -/
theorem integrableOn_weighted_optimizerField_respCell_respCoeffPlus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta) (a : CoeffSpace d) (i : Fin d) :
    MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i) V
    ∧ MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i) V := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    hconv.isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hgradC : MeasureTheory.IntegrableOn
      (fun x => (uP a).toH1.grad x i) (respCell jStar F t) := by
    have h := hdata.grad (Pi.single i 1) (aHarmonicFunctionOfAEEqCoeff hae (uP a))
    simpa [vecDot_single_left, grad_aHarmonicFunctionOfAEEqCoeff] using h
  have hfluxC : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uP a).toH1.grad x) i) (respCell jStar F t) := by
    have h := hdata.flux (Pi.single i 1) (aHarmonicFunctionOfAEEqCoeff hae (uP a))
    simpa [vecDot_single_left, grad_aHarmonicFunctionOfAEEqCoeff] using h
  have hgradV : MeasureTheory.IntegrableOn (fun x => (uP a).toH1.grad x i) V :=
    hgradC.mono_set hVU
  have hfluxV : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uP a).toH1.grad x) i) V := hfluxC.mono_set hVU
  have hfluxCoord : MeasureTheory.IntegrableOn
      (fun x => matVecMul ((respCoeffPlus F a) x) ((uP a).toH1.grad x) i) V := by
    refine hfluxV.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae.symm] with x hx
    rw [hx]
  have hK : IsCompact (closure (respCell jStar F t)) :=
    hconv.isBoundedDomain.isBounded.isCompact_closure
  have hVK : V ⊆ closure (respCell jStar F t) := fun x hx => subset_closure (hVU hx)
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hgradV hK hV hVK
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hfluxCoord hK hV hVK

end

end Homogenization.HighContrast.Multiscale
