import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cmp
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage

/-!
# The subcell average of the response integrand

The response integrand of a `b`-harmonic field expands pointwise as
`-(1/2) ∇v·b∇v - p·(b∇v) + q·∇v`.  Averaging this identity over an arbitrary measurable
subset `V` of the cell expresses the average of the response integrand as minus one half of
the average pathwise symmetric energy on `V`, plus the pairing of `(-p, q)` with the
slot-swapped cell average of the doubled optimizer field on `V`.  This is the algebraic
expansion behind the cell-average half of the response identity, stated on a subcell rather
than on the cell itself, which is what turns the subcell deficit of the first error row of
`p.response.transfer` into quantities that are measurable in the sample.

The general identity is stated for an arbitrary subcell `V ⊆ U` and the three integrability
facts it consumes; the two carrier specialisations run it on an aligned adapted subcell and
transport the result across the almost-everywhere elliptic representative of a response
coefficient.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The subcell average of the response integrand of a `b`-harmonic field on `U`: the average
over any subset `V ⊆ U` is minus one half of the average pathwise symmetric energy on `V`, plus
the pairing of `(-p, r)` with the slot-swapped average of the doubled optimizer field on `V`. -/
theorem volumeAverage_scalarResponseIntegrand_subset_eq_blockVecDot {d : ℕ} [NeZero d]
    {U V : Set (Vec d)} (hVU : V ⊆ U) {b : CoeffField d}
    (v : AHarmonicFunction b U) (p r : Vec d)
    (hEnergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand b v) V)
    (hFlux : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => matVecMul (b x) (v.toH1.grad x) i) V)
    (hGrad : ∀ i : Fin d, MeasureTheory.IntegrableOn (fun x => v.toH1.grad x i) V) :
    volumeAverage V (scalarResponseIntegrand U b p r v) =
      - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v)
        + blockVecDot (-p, r)
            (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) := by
  have _hVUsub : V ⊆ U := hVU
  have hA : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v)) V :=
    hEnergy.integrable.smul (-(1 / 2 : ℝ))
  have hF : MeasureTheory.IntegrableOn
      (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V := by
    have hsum : MeasureTheory.IntegrableOn
        (fun x => ∑ i, p i * matVecMul (b x) (v.toH1.grad x) i) V :=
      integrable_finsetSum Finset.univ (fun i _ => (hFlux i).const_mul (p i))
    simpa [vecDot] using hsum
  have hG : MeasureTheory.IntegrableOn (fun x => vecDot r (v.toH1.grad x)) V := by
    have hsum : MeasureTheory.IntegrableOn
        (fun x => ∑ i, r i * v.toH1.grad x i) V :=
      integrable_finsetSum Finset.univ (fun i _ => (hGrad i).const_mul (r i))
    simpa [vecDot] using hsum
  have hAB : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V :=
    hA.integrable.sub hF.integrable
  have hdecomp : scalarResponseIntegrand U b p r v =
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x)))) +
        (fun x => vecDot r (v.toH1.grad x)) := by
    funext x
    simp only [scalarResponseIntegrand, scalarVariationEnergyIntegrand, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomp, volumeAverage_add hAB hG, volumeAverage_sub hA hF, volumeAverage_smul]
  rw [volumeAverage_vecDot_left p (fun x => matVecMul (b x) (v.toH1.grad x)) hFlux,
    volumeAverage_vecDot_left r (fun x => v.toH1.grad x) hGrad]
  have hZ1 : (cellAverage V (optimizerField b v)).1
      = fun i => volumeAverage V (fun x => v.toH1.grad x i) := rfl
  have hZ2 : (cellAverage V (optimizerField b v)).2
      = fun i => volumeAverage V (fun x => matVecMul (b x) (v.toH1.grad x) i) := rfl
  have hs1 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).1
      = (cellAverage V (optimizerField b v)).2 := blockMatVecMul_blockSwap_fst _
  have hs2 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).2
      = (cellAverage V (optimizerField b v)).1 := blockMatVecMul_blockSwap_snd _
  rw [blockVecDot, hs1, hs2, hZ1, hZ2, vecDot_neg_left]
  ring

/-- The subcell average of the response integrand for the minus response coefficient, on an
aligned adapted subcell of the terminal cell: minus one half of the subcell energy plus the
pairing of `(-p, q^-)` with the slot-swapped subcell average of the doubled optimizer field.
The coefficient is transported from its almost-everywhere elliptic representative. -/
theorem volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) =
      - (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
        + blockVecDot (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
            (blockMatVecMul (blockSwap d)
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (uM a)))) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    rw [respCell, hs]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  set v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uM a)
    with hv
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hEnergy : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand f v) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (hdata.energy v).mono_set hVU
  have hFlux : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) (v.toH1.grad x) i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.flux (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hGrad : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => v.toH1.grad x i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.grad (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hmain := volumeAverage_scalarResponseIntegrand_subset_eq_blockVecDot hVU v
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) hEnergy hFlux hGrad
  have hresp : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) := by
    rw [hv]
    exact volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)
  have henergy : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand f v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
    rw [hv]
    exact volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae (uM a)
  have hcell : cellAverage (adaptedCellAtCenter (respGrid jStar F) s w) (optimizerField f v)
      = cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (uM a)) := by
    rw [hv]
    refine cellAverage_congr_ae hVU ?_
    filter_upwards [hae] with x hx
    simp only [optimizerField, grad_aHarmonicFunctionOfAEEqCoeff, hx]
  rw [hresp, henergy, hcell] at hmain
  exact hmain

/-- The plus twin of the subcell average identity, for the plus response coefficient and the
load `q^+`. -/
theorem volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) =
      - (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
        + blockVecDot (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
            (blockMatVecMul (blockSwap d)
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (uP a)))) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    rw [respCell, hs]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  set v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uP a)
    with hv
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hEnergy : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand f v) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (hdata.energy v).mono_set hVU
  have hFlux : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) (v.toH1.grad x) i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.flux (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hGrad : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => v.toH1.grad x i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.grad (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hmain := volumeAverage_scalarResponseIntegrand_subset_eq_blockVecDot hVU v
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) hEnergy hFlux hGrad
  have hresp : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) := by
    rw [hv]
    exact volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)
  have henergy : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand f v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
    rw [hv]
    exact volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae (uP a)
  have hcell : cellAverage (adaptedCellAtCenter (respGrid jStar F) s w) (optimizerField f v)
      = cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (uP a)) := by
    rw [hv]
    refine cellAverage_congr_ae hVU ?_
    filter_upwards [hae] with x hx
    simp only [optimizerField, grad_aHarmonicFunctionOfAEEqCoeff, hx]
  rw [hresp, henergy, hcell] at hmain
  exact hmain

end

end Homogenization.HighContrast.Multiscale
