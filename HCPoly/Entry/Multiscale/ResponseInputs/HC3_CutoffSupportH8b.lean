import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportFrame
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportFramePlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportRespW

/-!
# The annealed cutoff pairing bound for both signs under one constant

The cutoff pairing bound `e.response.cutoff.estimate` is an expectation, over the law of the
coefficient field, of the absolute volume average of the cutoff times the centred doubled optimizer
state.  The two signs of the recentring are handled by the separate frames
`exists_integral_abs_pairing_le_respWeak_of_pathwise` and
`exists_integral_abs_pairing_le_respWeakPlus_of_pathwise`, each with its own constant `C₀`.  This
file combines the two into a single statement carrying one strictly positive constant valid for
both signs simultaneously; the constant is `max C₀ 1`, which is positive and dominates the constant
of either frame, so each row is obtained by integrating the same pathwise hypothesis at `C₀` and
then relaxing it with the nonnegativity of the corresponding weak response energy `W^±`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The annealed cutoff pairing bound of `e.response.cutoff.estimate` for both signs under one
constant.  Given a nonnegative constant `C₀` and the deterministic pathwise estimate, at every
doubled block on the positive definite branch of the canonical metric and every admissible
coefficient, bounding the cutoff pairing of the centred doubled optimizer state by `C₀` times the
scale-weighted squared scale-average seminorm of the doubled optimizer state, there is a strictly
positive constant `C` such that for every probability law of the coefficient field, every selected
cell and cutoff, and every admissible family of cell maximizers for either recentring, the
expectation of the absolute pairing is at most `C` times the weak response energy `W^-` for the
minus sign and at most `C` times `W^+` for the plus sign.  The constant may be taken to be
`max C₀ 1`. -/
theorem exists_pos_const_integral_abs_pairing_le_respWeak (d : ℕ) [NeZero d]
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
    ∃ C : ℝ, 0 < C ∧
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
          ∀ uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
            (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) →
            Integrable (fun a => besovSeminorm t (fun n z =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                    (optimizerField (respCoeffPlus F a) (uP a)) -
                  respYPlus P jStar F t e)) ^ 2) P →
          (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1
                  - (respYMinus P jStar F t e).1)
                ((optimizerField (respCoeffMinus F a) (uM a) x).2
                  - (respYMinus P jStar F t e).2))| ∂P) ≤ C * respWMinus P jStar F t e ∧
            (∫ a, |volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField (respCoeffPlus F a) (uP a) x).1
                  - (respYPlus P jStar F t e).1)
                ((optimizerField (respCoeffPlus F a) (uP a) x).2
                  - (respYPlus P jStar F t e).2))| ∂P) ≤ C * respWPlus P jStar F t e := by
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1), ?_⟩
  intro P _ jStar F t e φ hjStar hφ uM huM hIntM uP huP hIntP
  have hminus := exists_integral_abs_pairing_le_respWeak_of_pathwise d C₀ hC₀ hpath
    P jStar F t e φ hjStar hφ uM huM hIntM
  have hplus := exists_integral_abs_pairing_le_respWeakPlus_of_pathwise d C₀ hC₀ hpath
    P jStar F t e φ hjStar hφ uP huP hIntP
  exact ⟨le_trans hminus (mul_le_mul_of_nonneg_right (le_max_left C₀ 1)
      (respWMinus_nonneg P jStar F t e)),
    le_trans hplus (mul_le_mul_of_nonneg_right (le_max_left C₀ 1)
      (respWPlus_nonneg P jStar F t e))⟩

end

end Homogenization.HighContrast.Multiscale
