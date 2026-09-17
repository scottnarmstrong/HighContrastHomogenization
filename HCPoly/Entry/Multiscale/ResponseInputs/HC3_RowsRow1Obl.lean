import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Disch
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1DischPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsObligations

/-!
# The first error row of `p.response.transfer` as the named obligation

The cutoff estimate of `e.response.cutoff.estimate` consumes the first error row of
`p.response.transfer` — the cost of replacing the terminal optimizer by the coarse-cell
optimizers — in the predicate form `CutoffEnergyDefectRowMinus`, and its adjoint twin
`CutoffEnergyDefectRowPlus`.  On the response carriers that row is the replacement bound with the
explicit dimensional constant `max 3 (32 d^2 responseCutoffProfileConst)`.

The two declarations here restate the carrier bounds of `HC3_DirectRow1Disch` and
`HC3_DirectRow1DischPlus` directly as those predicates, so that the row assembly of the cutoff
estimate can consume them without unfolding the predicate at each use site.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The first error row of `p.response.transfer` on the response carriers, as
`CutoffEnergyDefectRowMinus`.**  Under the hypotheses of the carrier bound, the law-integral of the
cutoff half-energy of the terminal optimizer minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-]`, which is exactly the named obligation
`CutoffEnergyDefectRowMinus` used by `e.response.cutoff.estimate`. -/
theorem cutoffEnergyDefectRowMinus_of_carriers {d : ℕ} [NeZero d]
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
    CutoffEnergyDefectRowMinus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uM := by
  unfold CutoffEnergyDefectRowMinus
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus_of_carriers P hstat jStar hjStar F hm
    H s t ht hjs e φ hφ uM hmax hblk hJt hJs hDint hEint hWint

/-- **The first error row of `p.response.transfer` on the response carriers, as
`CutoffEnergyDefectRowPlus`.**  This is the adjoint-sign twin of
`cutoffEnergyDefectRowMinus_of_carriers`: under the hypotheses of the carrier bound for the
terminal optimizer `uP` of the adjoint recentred coefficient, the law-integral of the cutoff
half-energy of `uP` minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^+ + (τ^+ E[J_t^+])^{1/2} + 3^{-H} E[J_t^+]`, which is exactly the named obligation
`CutoffEnergyDefectRowPlus` used by `e.response.cutoff.estimate`. -/
theorem cutoffEnergyDefectRowPlus_of_carriers {d : ℕ} [NeZero d]
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
    CutoffEnergyDefectRowPlus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uP := by
  unfold CutoffEnergyDefectRowPlus
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus_of_carriers P hstat jStar hjStar F hm
    H s t ht hjs e φ hφ uP hmax hblk hJt hJs hDint hEint hWint

end

end Homogenization.HighContrast.Multiscale
