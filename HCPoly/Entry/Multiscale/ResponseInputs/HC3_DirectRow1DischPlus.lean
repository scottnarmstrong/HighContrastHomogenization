import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1CellPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Hid
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Osc
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cmp
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectTauIdentity
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectStatCell
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectSubcellBlk
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectMeanCancel
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCutoffWeights
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectDeficitNonneg
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# The first error row on the carriers, side conditions discharged (adjoint sign)

The first error row of `p.response.transfer` is proved in the adjoint configuration by
`abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus` from fifteen hypotheses.  Every one of them
that is a pathwise statement — the energy-defect identity, the oscillation split, the subcell
comparison, the two cutoff-weight facts, the three signs, the stationarity of the annealed subcell
response and the scale-defect identity — is available on the carriers of the cutoff estimate
without any pointwise ellipticity hypothesis, because a coefficient of the carrier is elliptic only
almost everywhere and the transport along an a.e.-elliptic representative has been built.  This
module assembles those statements and leaves only the sample integrabilities as hypotheses:

* the terminal and coarse pathwise responses are `P`-integrable;
* the subcell response deficits and the averaged optimizer energies are `P`-integrable;
* the cutoff-weighted optimizer energy is `P`-integrable.

The conclusion is the printed bound
`C (τ^+ + (τ^+ E[J_t^+])^{1/2} + 3^{-H} E[J_t^+])` with the explicit dimensional constant
`C = max 3 (32 d^2 responseCutoffProfileConst)`.

Paper: `p.response.transfer`.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal-optimizer replacement row on the cutoff carriers, adjoint sign, side
conditions discharged.**  Under a stationary probability law on the coefficient carrier, let `uP`
be a terminal optimizer for the adjoint recentred coefficient `a_+ = aᵗ + g`, `φ` a cutoff of the
response class, and suppose the annealed pathwise responses at the terminal and coarse scales are
`P`-integrable, the subcell response deficits, the averaged subcell optimizer energies and the
cutoff-weighted optimizer energy are `P`-integrable.  Then the law-integral of the cutoff
half-energy of `uP` minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^+ + (τ^+ E[J_t^+])^{1/2} + 3^{-H} E[J_t^+]`.  All pathwise side conditions are supplied by the
a.e.-elliptic representative transport, so no pointwise ellipticity is assumed.  This is the first
error row of `p.response.transfer` on the carriers of the cutoff estimate. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus_of_carriers {d : ℕ} [NeZero d]
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
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hDint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hEint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P)
    (hWint : Integrable (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P) :
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    have hpos : 0 < (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal := by
      rw [Geometry.volume_adaptedCell_toReal]
      have hdet : 0 < |(respGrid jStar F).det| := abs_pos.mpr (by
        have hunit := (Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq
        exact IsUnit.ne_zero hunit)
      positivity
    exact ne_of_gt hpos
  have hid : ∀ a, cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) :=
    fun a => cutoffHalfEnergyAux_sub_respJ_eq_respCoeffPlus hjStar hm t φ hφ
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) (hmax a)
  have hosc : ∀ a, |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
          - (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)) := by
    intro a
    have h := abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffPlus hjStar hm t H hφ
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) (hmax a)
    simpa only [hts] using h
  have hcmp : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
          - ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)|
        ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
          + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) *
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))) := by
    intro w hw a
    have h := abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffPlus hjStar hm t H
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) hw
    simpa only [hts] using h
  have hc0 : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0 := by
    have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ
      (by
        simpa only [b130_adaptedCellAtCenter_zero] using
          integrableOn_sub_one_isResponseCutoff hq hφ t 0)
      hvol
      (by
        simpa only [b130_adaptedCellAtCenter_zero] using
          integrableOn_isResponseCutoff hq hφ t 0)
    simpa only [hts] using h
  have hc1 : ∀ w ∈ triadicIndexBox d H,
      |volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)| ≤ 1 :=
    fun w _ => abs_volumeAverage_sub_one_isResponseCutoff_le_one hq hφ s w
  have hJ0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    intro w hw a
    have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffPlus hjStar hm t H
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) hw).1
    simpa only [hts] using h
  have hD0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) := by
    intro w hw a
    have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffPlus hjStar hm t H
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) hw).2
    simpa only [hts] using h
  have hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uP a)
    have hmaxf : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) f v :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hmax a)
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      hconv.isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hJf : 0 ≤ ResponseJ (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) f :=
      responseJ_nonneg_of_isResponseMaximizer hEll
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v hmaxf
        (hdata.weakFlux v)
        (hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v)
        (hdata.firstVariation (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v v)
        (hdata.energy v)
    have hJplus : 0 ≤ ResponseJ (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) := by
      rw [responseJ_congr_of_ae_eq hae (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e)]
      exact hJf
    simpa only [respJ] using! hJplus
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P :=
    fun w _ => integrable_responseJ_respCoeffPlus_adaptedCellAtCenter P hq F s w
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk s w)
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P := by
    intro w hw
    have heq : (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
        = fun a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
            - (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) := by
      funext a
      ring
    rw [heq]
    exact (hJint w hw).sub (hDint w hw)
  have hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv : MeasureTheory.IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (aHarmonicFunctionOfAEEqCoeff hae (uP a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (aHarmonicFunctionOfAEEqCoeff hae (uP a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (aHarmonicFunctionOfAEEqCoeff hae (uP a)) hv
  have hJval : ∀ w ∈ triadicIndexBox d H,
      (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
        = ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P := by
    intro w _
    have hw' := integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs w
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk s w)
    have h0 := integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs 0
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk s 0)
    rw [b130_adaptedCellAtCenter_zero (respGrid jStar F) s] at h0
    have hcJs : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
        = blockResponseEnergy (blockCongr (h68_respGPlus F) (respMean P jStar F s))
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) := by
      simpa only [respJ] using h0
    rw [hcJs]
    exact hw'
  have hDval : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = respTauPlus P jStar F s t e :=
    integral_avsum_subcellDeficit_eq_respTauPlus P hstat jStar hjStar F hm H s t ht hjs e uP hmax
      (fun w => hblk s w) hrespint hJint hRint hJt hJs
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus (d := d) P jStar F H s t e φ uP
    hid hosc hcmp hc0 hc1 hJ0 hD0 hJt0 hJint hDint hEint hWint hJt hJval hDval

end

end Homogenization.HighContrast.Multiscale
