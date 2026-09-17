import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECongr
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffEnergyDefect
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectExpansionInt

/-!
# The cutoff energy defect at an almost-everywhere elliptic coefficient

The response identity `cutoffHalfEnergy_sub_respJ_eq` identifies the cutoff energy defect
`cutoffHalfEnergyAux - respJ` with half the `(φ - 1)`-weighted optimizer energy, but only for a
coefficient that is pointwise elliptic on the cell.  The two coefficient fields of the response
problem, `respCoeffMinus F a` and `respCoeffPlus F a`, are elliptic only almost everywhere: a point
of `CoeffSpace d` is an a.e. class, and no representative is elliptic pointwise.

The identity is nevertheless invariant under an a.e. replacement of the coefficient, because
carrying a harmonic function along the replacement leaves its gradient — and hence both the
cutoff half-energy and the pathwise response — unchanged.  Running the pointwise identity at the
elliptic representative supplied by `exists_elliptic_representative_respCell_respCoeffMinus` and
transporting back gives the defect identity verbatim for the carrier coefficient and the given
maximizer:

* `cutoffHalfEnergyAux_sub_respJ_eq_respCoeffMinus` — the minus family `a_- = a - g`;
* `cutoffHalfEnergyAux_sub_respJ_eq_respCoeffPlus` — the adjoint twin `a_+ = a^t + g`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The doubled optimizer energy `⟨Z₁, Z₂⟩ = ∇v · b ∇v` agrees pointwise with the variation energy
`∇v · (symmPart b) ∇v`, since the antisymmetric part of `b` contributes nothing to the quadratic
form. -/
private theorem vecDot_optimizerField_eq_scalarVariationEnergyIntegrand {d : ℕ}
    (b : CoeffField d) {U : Set (Vec d)} (v : AHarmonicFunction b U) :
    (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = scalarVariationEnergyIntegrand b v := by
  funext x
  simp only [optimizerField, scalarVariationEnergyIntegrand]
  exact (vecDot_matVecMul_symmPart (b x) (v.toH1.grad x)).symm

/-- The cutoff energy defect identity at a pointwise elliptic coefficient that agrees almost
everywhere with the carrier coefficient.  The maximizer `u` for the carrier coefficient `c` is
carried along the a.e. equality to a maximizer for the elliptic representative `f`; the identity
`cutoffHalfEnergy_sub_respJ_eq` is applied there and every quantity is transported back across the
a.e. equality.  Both sides are unchanged by the replacement, so the conclusion names `c` and `u`. -/
private theorem cutoffHalfEnergyAux_sub_respJ_eq_of_ae_eq {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) {c f : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : c =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff q t φ) (p r : Vec d)
    (u : AHarmonicFunction c (HighContrast.adaptedCell q t))
    (hmax : IsResponseMaximizer (HighContrast.adaptedCell q t) p r c u) :
    cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ c u - respJ q t p r c
      = (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand c u x) := by
  have hconv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  let v : AHarmonicFunction f (HighContrast.adaptedCell q t) :=
    aHarmonicFunctionOfAEEqCoeff hae u
  have hmaxf : IsResponseMaximizer (HighContrast.adaptedCell q t) p r f v :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hconv.isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (HighContrast.adaptedCell q t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hu_int : weakFluxIntegrable (HighContrast.adaptedCell q t) f v := hdata.weakFlux v
  have hresp_u :
      IntegrableOn (scalarResponseIntegrand (HighContrast.adaptedCell q t) f p r v)
        (HighContrast.adaptedCell q t) :=
    hdata.response p r v
  have hlin_self :
      IntegrableOn (scalarFirstVariationIntegrand (HighContrast.adaptedCell q t) f p r v v)
        (HighContrast.adaptedCell q t) :=
    hdata.firstVariation p r v v
  have henergy : IntegrableOn (scalarVariationEnergyIntegrand f v) (HighContrast.adaptedCell q t) :=
    hdata.energy v
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hφb : ∀ x, |φ x| ≤ 2 := fun x => by
    rw [abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hvecD : (fun x => vecDot (optimizerField f v x).1 (optimizerField f v x).2)
      = scalarVariationEnergyIntegrand f v :=
    vecDot_optimizerField_eq_scalarVariationEnergyIntegrand f v
  have hD_int :
      IntegrableOn (fun x => vecDot (optimizerField f v x).1 (optimizerField f v x).2)
        (HighContrast.adaptedCell q t) := by
    rw [hvecD]
    exact henergy
  have hφD :
      IntegrableOn (fun x => φ x * vecDot (optimizerField f v x).1 (optimizerField f v x).2)
        (HighContrast.adaptedCell q t) :=
    integrableOn_cutoff_mul_coord hconv.isOpen.measurableSet hconv.volume_lt_top.ne hφm
      hφb hD_int
  have hkey := cutoffHalfEnergy_sub_respJ_eq (q := q) hq t hEll φ p r v hmaxf
    hu_int hresp_u hlin_self henergy hφD
  have hvecφ : (fun x => φ x * vecDot (optimizerField f v x).1 (optimizerField f v x).2)
      = fun x => φ x * scalarVariationEnergyIntegrand f v x := by
    funext x
    rw [congrFun hvecD x]
  have hvecψ :
      (fun x => (φ x - 1) * vecDot (optimizerField f v x).1 (optimizerField f v x).2)
        = fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x := by
    funext x
    rw [congrFun hvecD x]
  rw [hvecφ, hvecψ] at hkey
  have hkeyE : cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ f v - respJ q t p r f
      = (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x) := by
    unfold cutoffHalfEnergyAux
    rw [hvecφ]
    exact hkey
  have hcut : cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ f v
      = cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ c u :=
    cutoffHalfEnergyAux_aHarmonicFunctionOfAEEqCoeff (U := HighContrast.adaptedCell q t) hae φ u
  have hrespJ : respJ q t p r c = respJ q t p r f := by
    unfold respJ
    exact responseJ_congr_of_ae_eq_subset (U := HighContrast.adaptedCell q t)
      (V := HighContrast.adaptedCell q t) subset_rfl hae p r
  have hLHS : cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ c u - respJ q t p r c
      = cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ f v - respJ q t p r f := by
    rw [← hcut, hrespJ]
  have hRHS : volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      = volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand c u x) :=
    volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (U := HighContrast.adaptedCell q t) (V := HighContrast.adaptedCell q t) subset_rfl hae
      (fun x => φ x - 1) u
  rw [hLHS, hkeyE, hRHS]

/-- The cutoff energy defect of the minus family, with no pointwise ellipticity hypothesis. -/
theorem cutoffHalfEnergyAux_sub_respJ_eq_respCoeffMinus {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffMinus F a) u) :
    cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) u
        - respJ (respGrid jStar F) t p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  exact cutoffHalfEnergyAux_sub_respJ_eq_of_ae_eq (q := respGrid jStar F) hq t hEll hae
    φ hφ p r u hmax

/-- The adjoint twin. -/
theorem cutoffHalfEnergyAux_sub_respJ_eq_respCoeffPlus {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffPlus F a) u) :
    cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) u
        - respJ (respGrid jStar F) t p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  exact cutoffHalfEnergyAux_sub_respJ_eq_of_ae_eq (q := respGrid jStar F) hq t hEll hae
    φ hφ p r u hmax

end

end Homogenization.HighContrast.Multiscale
