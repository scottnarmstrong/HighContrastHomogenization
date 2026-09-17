import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportIntegrate
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportDegenInt
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# The annealed cutoff pairing bound from its pathwise form

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the expectation, over
the sample law, of the absolute value of the volume average over the selected cell of the
cutoff-weighted pairing of the centred optimizer field with the recentring vector.  This file
reduces the annealed bound to its pathwise form: assuming the deterministic estimate at every
sample, the singular-grid branch is discharged by the degeneration of the adapted cell (every
volume average collapses to the junk value `0`) and the positive-definite branch by monotonicity
of the Bochner integral, so that only the pathwise estimate remains as a hypothesis.  This is the
annealed form of `e.response.cutoff.estimate`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The annealed cutoff pairing bound `e.response.cutoff.estimate`, reduced to the pathwise
estimate `hpath`: if at every sample and for every elliptic data the pairing average is dominated
by `C₀` times the scale-weighted squared scale-average seminorm of the doubled optimizer state,
and that seminorm square is Bochner integrable, then the expectation of the absolute pairing is at
most `C₀` times the weak response energy `W^-`.  The dichotomy
`metric_posDef_or_respGrid_det_eq_zero` splits the proof: on the singular-grid branch the adapted
cell is Lebesgue null and the integral vanishes, while on the positive-definite branch the
pathwise bound is integrated against the law. -/
theorem exists_integral_abs_pairing_le_respWeak_of_pathwise (d : ℕ) [NeZero d]
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
      ∀ uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t),
        (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) →
        Integrable (fun a => besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffMinus F a) (uM a)) -
              respYMinus P jStar F t e)) ^ 2) P →
        (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
            φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
                - (respYMinus P jStar F t e).1)
              ((optimizerField (respCoeffMinus F a) (uM a) x).2
                - (respYMinus P jStar F t e).2))| ∂P)
          ≤ C₀ * respWMinus P jStar F t e := by
  intro P _ jStar F t e φ hjStar hφ uM hu hintegrable
  rcases metric_posDef_or_respGrid_det_eq_zero jStar F with hm | hdet
  · -- Positive-definite branch: integrate the pathwise bound against the law.
    let G : CoeffSpace d → ℝ := fun a => volumeAverage (respCell jStar F t) (fun x =>
      φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
          - (respYMinus P jStar F t e).1)
        ((optimizerField (respCoeffMinus F a) (uM a) x).2
          - (respYMinus P jStar F t e).2))
    have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
    have hbdd : BddAbove (respWeakEnergySet P (respGrid jStar F) t (respM0 F)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
        (respYMinus P jStar F t e)) :=
      bddAbove_respWeakEnergySet_respWMinus P jStar F t e hgrid
    have hptwise : ∀ a : CoeffSpace d, |G a| ≤
        C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField (respCoeffMinus F a) (uM a)) - respYMinus P jStar F t e)) ^ 2) := by
      intro a
      exact hpath jStar F t φ hjStar hφ hm (respCoeffMinus F a) (respYMinus P jStar F t e) (uM a)
        (exists_elliptic_representative_respCoeffMinus (respGrid jStar F) hgrid t F a)
    exact integral_abs_le_respWeakEnergy_of_pathwise P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
      (respYMinus P jStar F t e) G C₀ hC₀ hbdd uM hu hintegrable hptwise
  · -- Singular-grid branch: the adapted cell is null, so every average is the junk value `0`.
    have hzero : (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
            - (respYMinus P jStar F t e).1)
          ((optimizerField (respCoeffMinus F a) (uM a) x).2
            - (respYMinus P jStar F t e).2))| ∂P) = 0 := by
      simpa only [respCell] using
        (integral_abs_volumeAverage_adaptedCell_eq_zero_of_det_eq_zero (P := P)
          (q := respGrid jStar F) hdet t (fun a x => φ x * vecDot
            ((optimizerField (respCoeffMinus F a) (uM a) x).1 - (respYMinus P jStar F t e).1)
            ((optimizerField (respCoeffMinus F a) (uM a) x).2 - (respYMinus P jStar F t e).2)))
    rw [hzero]
    exact mul_nonneg hC₀ (respWeakEnergy_nonneg P (respGrid jStar F) t (respM0 F)
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
      (respYMinus P jStar F t e))

end

end Homogenization.HighContrast.Multiscale
