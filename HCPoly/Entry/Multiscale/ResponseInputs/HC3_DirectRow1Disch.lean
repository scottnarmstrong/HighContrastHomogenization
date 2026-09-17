import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cell
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
# The first error row of `p.response.transfer` on the carriers, side conditions discharged

The terminal-optimizer replacement row of `p.response.transfer` compares the cutoff half-energy of
the terminal optimizer with the terminal response, integrated over the law of coefficients.  The
assembly `abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus` states that comparison with every
pathwise ingredient as a hypothesis.  This module supplies those ingredients on the coefficient
carriers: the energy-defect identity, the oscillation split over the coarse subdivision, the subcell
comparison, the two cutoff-weight facts, the three signs, the subcell-response integrabilities, the
common annealed subcell value and the identification of the flat mean deficit with the scale defect.
Only the sample integrabilities and the positivity of the canonical metric remain as hypotheses; no
pointwise ellipticity is assumed, because the a.e.-elliptic representative transport produces every
pathwise statement on the carriers.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The first error row of `p.response.transfer` on the response carriers.**  Let `P` be a
stationary probability law on the coefficient space, `F` a block matrix with positive definite
canonical metric, `jStar` a scale with `2 d ≤ 3 ^ jStar`, and `s ≤ t = s + H` two scales with
`jStar ≤ s`.  For a cutoff `φ` of the response class at the terminal scale and a family `uM` of
terminal maximizers for the recentred coefficients, assume that every coarse block of the sample is
integrable on every aligned cell, that the terminal and coarse pathwise responses are `P`-integrable,
and that the subcell deficit, the subcell energy and the `(φ - 1)`-weighted terminal energy have
`P`-integrable flat means.  Then the law-integral of the cutoff half-energy of the terminal optimizer
minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-]`, the printed first error row of
`p.response.transfer`.  The pathwise side conditions of the row are discharged here; the
integrability of the sample data is the only remaining input. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus_of_carriers {d : ℕ} [NeZero d]
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
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hDint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P)
    (hEint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P)
    (hWint : Integrable (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P) :
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by
    rw [ht]
    ring
  have hint : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h := integrableOn_sub_one_isResponseCutoff hq hφ t 0
    rwa [b130_adaptedCellAtCenter_zero (respGrid jStar F) t] at h
  have hφint : IntegrableOn φ (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h := integrableOn_isResponseCutoff hq hφ t 0
    rwa [b130_adaptedCellAtCenter_zero (respGrid jStar F) t] at h
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    rw [Geometry.volume_adaptedCell_toReal]
    exact mul_ne_zero
      (ne_of_gt (abs_pos.mpr
        (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq))))
      (ne_of_gt (by positivity : (0 : ℝ) < ((3 : ℝ) ^ t) ^ d))
  have hrespint : ∀ a, IntegrableOn (scalarResponseIntegrand (respCell jStar F t)
      (respCoeffMinus F a) (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (uM a)) (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv := hdata.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (aHarmonicFunctionOfAEEqCoeff hae (uM a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _) hae.symm
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (aHarmonicFunctionOfAEEqCoeff hae (uM a)) hv
  have hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uM a)
    have hmaxf : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f v :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae _ _ (hmax a)
    have hnonneg : 0 ≤ ResponseJ (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f :=
      responseJ_nonneg_of_isResponseMaximizer hEll _ _ v hmaxf
        (hdata.weakFlux v) (hdata.response _ _ v) (hdata.firstVariation _ _ v v) (hdata.energy v)
    have hcongr : respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)
        = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f := by
      unfold respJ
      exact responseJ_congr_of_ae_eq hae _ _
    rw [hcongr]
    simpa only [respJ, respCell] using hnonneg
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P :=
    fun w _ => integrable_responseJ_respCoeffMinus_adaptedCellAtCenter P hq F s w _ _ (hblk s w)
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P := by
    intro w hw
    refine ((hJint w hw).sub (hDint w hw)).congr ?_
    filter_upwards with a
    simp only [Pi.sub_apply]
    ring
  have hJs_eq : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      = blockResponseEnergy (blockCongr (respG F) (respMean P jStar F s))
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) := by
    have h0 := integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs 0
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (hblk s 0)
    rw [b130_adaptedCellAtCenter_zero (respGrid jStar F) s] at h0
    simpa only [respJ] using h0
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus (P := P) jStar F H s t e φ uM
    (fun a => cutoffHalfEnergyAux_sub_respJ_eq_respCoeffMinus hjStar hm t φ hφ
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) a (uM a) (hmax a))
    (fun a => by
      have h := abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffMinus (jStar := jStar)
        (F := F) hjStar hm t H hφ (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        a (uM a) (hmax a)
      simpa only [hts] using h)
    (fun w hw a => by
      have h := abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffMinus (jStar := jStar)
        (F := F) hjStar hm t H (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        a (uM a) hw
      simpa only [hts] using h)
    (by
      have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ hint hvol hφint
      simpa only [hts] using h)
    (fun w hw => abs_volumeAverage_sub_one_isResponseCutoff_le_one hq hφ s w)
    (fun w hw a => by
      have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffMinus (jStar := jStar) (F := F)
        hjStar hm t H (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) a (uM a) hw).1
      simpa only [hts] using h)
    (fun w hw a => by
      have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffMinus (jStar := jStar) (F := F)
        hjStar hm t H (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) a (uM a) hw).2
      simpa only [hts] using h)
    hJt0 hJint hDint hEint hWint hJt
    (fun w hw => (integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs w
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (hblk s w)).trans hJs_eq.symm)
    (integral_avsum_subcellDeficit_eq_respTauMinus P hstat jStar hjStar F hm H s t ht hjs e uM hmax
      (fun w => hblk s w) hrespint hJint hRint hJt hJs)

end

end Homogenization.HighContrast.Multiscale
