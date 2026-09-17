import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectSubcellBlk
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cmp

/-!
# The flat sum of the subcell deficits of the first error row

The subcell deficit of the first error row of `p.response.transfer` is the amount by which the
terminal optimizer fails to maximize the response on an aligned subcell of the coarse scale.
Exact partition averaging collapses the flat average of the subcell averages of the response
integrand of the terminal optimizer to its average over the terminal cell, which at a maximizer
is the terminal response.  Hence the flat average of the subcell deficits is the flat average of
the subcell responses minus the terminal response, an identity between quantities each of which
is a fixed linear functional of the coarse blocks of the sample and is therefore `P`-integrable.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The flat sum of the subcell deficits is the flat sum of the subcell responses minus the
terminal response, minus sign.**  On each aligned subcell of the coarse scale the first error row
of `p.response.transfer` measures the response of the sample against the subcell average of the
response integrand of the terminal optimizer.  The subcells partition the terminal cell and all
have the same volume, so the normalized sum of those averages is the terminal cell average, which
at a maximizer is the terminal response `J_t^-`.  Therefore the normalized sum of the subcell
deficits equals the normalized sum of the subcell responses minus `J_t^-`. -/
theorem avsum_subcellDeficit_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
      = (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
          ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by
    rw [ht]
    ring
  have hf : IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (aHarmonicFunctionOfAEEqCoeff hae (uM a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (aHarmonicFunctionOfAEEqCoeff hae (uM a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (aHarmonicFunctionOfAEEqCoeff hae (uM a)) hv
  have hpart := avsum_volumeAverage_eq (respGrid jStar F) hq t H
    (f := scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) hf
  have hpart' : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := by
    rw [show (∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
        = ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) by
      exact Finset.sum_congr rfl (fun w _ => by rw [hts])] at hpart
    rw [hpart]
    simpa only [respJ, respCell] using
      (responseJ_eq_of_isResponseMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respCoeffMinus F a) (hmax a)).symm
  rw [Finset.sum_sub_distrib, mul_sub, hpart']

/-- **The flat sum of the subcell deficits is the flat sum of the subcell responses minus the
terminal response, plus sign.**  The transposed twin of `avsum_subcellDeficit_respCoeffMinus_eq`:
the coefficient family `a_+ = aᵀ + g`, the dual load `q^+` and the terminal optimizer family `uP`
replace their minus-sign counterparts, and the terminal response is `J_t^+`. -/
theorem avsum_subcellDeficit_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
      = (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
          ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by
    rw [ht]
    ring
  have hf : IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (aHarmonicFunctionOfAEEqCoeff hae (uP a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (aHarmonicFunctionOfAEEqCoeff hae (uP a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (aHarmonicFunctionOfAEEqCoeff hae (uP a)) hv
  have hpart := avsum_volumeAverage_eq (respGrid jStar F) hq t H
    (f := scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) hf
  have hpart' : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    rw [show (∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
        = ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) by
      exact Finset.sum_congr rfl (fun w _ => by rw [hts])] at hpart
    rw [hpart]
    simpa only [respJ, respCell] using
      (responseJ_eq_of_isResponseMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respCoeffPlus F a) (hmax a)).symm
  rw [Finset.sum_sub_distrib, mul_sub, hpart']

/-- **Integrability of the flat sum of the subcell responses, minus sign.**  Each aligned subcell
response of the recentred coefficient `a_-` is `P`-integrable when the coarse blocks of the sample
are, so the normalized sum over the triadic index box is `P`-integrable as well. -/
theorem integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s : ℤ) (p r : Vec d)
    (hblk : ∀ w : Fin d → ℤ, HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w)) :
    MeasureTheory.Integrable (fun a => (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) p r
        (respCoeffMinus F a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  exact (integrable_finsetSum (triadicIndexBox d H) fun w _ =>
    integrable_responseJ_respCoeffMinus_adaptedCellAtCenter P hq F s w p r (hblk w)).const_mul _

/-- **Integrability of the flat sum of the subcell responses, plus sign.**  The transposed twin of
`integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffMinus`, with the coefficient family `a_+`
instead of `a_-`. -/
theorem integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s : ℤ) (p r : Vec d)
    (hblk : ∀ w : Fin d → ℤ, HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w)) :
    MeasureTheory.Integrable (fun a => (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) p r
        (respCoeffPlus F a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  exact (integrable_finsetSum (triadicIndexBox d H) fun w _ =>
    integrable_responseJ_respCoeffPlus_adaptedCellAtCenter P hq F s w p r (hblk w)).const_mul _

end

end Homogenization.HighContrast.Multiscale
