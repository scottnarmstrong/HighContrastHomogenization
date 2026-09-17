import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportIntegrate
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportDegenInt
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportFrame

/-!
# The annealed plus-sign cutoff pairing bound from its pathwise form

The cutoff pairing bound `e.response.cutoff.estimate` is an expectation, over the law of the
coefficient field, of the absolute volume average of the cutoff times the centred doubled
optimizer state.  This file reduces that annealed estimate to its deterministic pathwise form on
the plus-sign branch: the metric dichotomy splits off the singular-grid branch, where every
volume average is the junk value `0`, and on the positive definite branch a pathwise estimate at
each sample is passed through the integral by monotonicity together with the nonnegativity of the
weak response energy.  What remains is a single deterministic inequality, hypothesis `hpath`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The annealed cutoff pairing bound of `e.response.cutoff.estimate`, reduced to its pathwise
form.  Suppose that, for every doubled block on the positive definite branch of the canonical
metric and every admissible coefficient, the cutoff pairing of the centred doubled optimizer
state obeys the deterministic estimate with constant `C₀`.  Then for every probability law of the
coefficient field and every admissible family of cell maximizers, the expectation of the absolute
pairing is at most `C₀` times the weak response energy `W^+`.  The probabilistic content and the
singular-grid branch of the metric dichotomy are discharged here, so the only remaining input is
the pathwise estimate. -/
theorem exists_integral_abs_pairing_le_respWeakPlus_of_pathwise (d : ℕ) [NeZero d]
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpath : ∀ (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ),
      2 * d ≤ 3 ^ jStar → IsResponseCutoff (respGrid jStar F) t φ →
      (explicitCanonicalMetric F).PosDef →
      ∀ (b : CoeffField d) (Y : BlockVec d)
        (u : AHarmonicFunction b (respCell jStar F t)),
        (∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
          IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
            b =ᵐ[volumeMeasureOn (respCell jStar F t)] f) →
        |volumeAverage (respCell jStar F t) (fun x =>
            φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))| ≤
          C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField b u) - Y)) ^ 2)) :
    ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
      (t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
      2 * d ≤ 3 ^ jStar →
      IsResponseCutoff (respGrid jStar F) t φ →
      ∀ uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
        (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) (uM a)) →
        Integrable (fun a => besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffPlus F a) (uM a)) -
              respYPlus P jStar F t e)) ^ 2) P →
        (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
            φ x * vecDot ((optimizerField (respCoeffPlus F a) (uM a) x).1
                - (respYPlus P jStar F t e).1)
              ((optimizerField (respCoeffPlus F a) (uM a) x).2
                - (respYPlus P jStar F t e).2))| ∂P)
          ≤ C₀ * respWPlus P jStar F t e := by
  intro P hP jStar F t e φ hjStar hφ uM hu hintegrable
  rcases metric_posDef_or_respGrid_det_eq_zero jStar F with hm | hdet
  · have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
    have hmain := integral_abs_le_respWeakEnergy_of_pathwise P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F)
      (respYPlus P jStar F t e)
      (fun a => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffPlus F a) (uM a) x).1
            - (respYPlus P jStar F t e).1)
          ((optimizerField (respCoeffPlus F a) (uM a) x).2
            - (respYPlus P jStar F t e).2)))
      C₀ hC₀ (bddAbove_respWeakEnergySet_respWPlus P jStar F t e hgrid) uM hu hintegrable
      (fun a => hpath jStar F t φ hjStar hφ hm (respCoeffPlus F a) (respYPlus P jStar F t e)
        (uM a) (exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a))
    simpa only [respWPlus] using hmain
  · have hzero : (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffPlus F a) (uM a) x).1
            - (respYPlus P jStar F t e).1)
          ((optimizerField (respCoeffPlus F a) (uM a) x).2
            - (respYPlus P jStar F t e).2))| ∂P) = 0 := by
      simpa only [respCell] using
        integral_abs_volumeAverage_adaptedCell_eq_zero_of_det_eq_zero P hdet t
          (fun a x => φ x * vecDot
            ((optimizerField (respCoeffPlus F a) (uM a) x).1 - (respYPlus P jStar F t e).1)
            ((optimizerField (respCoeffPlus F a) (uM a) x).2 - (respYPlus P jStar F t e).2))
    rw [hzero]
    simpa only [respWPlus] using mul_nonneg hC₀ (respWeakEnergy_nonneg P (respGrid jStar F) t
      (respM0 F) (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F)
      (respYPlus P jStar F t e))

end

end Homogenization.HighContrast.Multiscale
