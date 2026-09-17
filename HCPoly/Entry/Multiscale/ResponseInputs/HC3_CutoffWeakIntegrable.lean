import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffEnvelopeIntegrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of the squared weak-quantity seminorm

The weak-quantity estimate `e.response.weak.estimate` bounds the squared scale-average Besov
seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state by a sample-dependent
envelope.  This file records the elementary measure-theoretic consequence used to discharge the
integrability premise of the cutoff rows: a measurable nonnegative function dominated almost
everywhere by an integrable function is integrable.

The generic domination statement is specialised to the all-scale envelope
`respAllScaleMax` of `HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffEnvelopeIntegrable`, whose
`Q`-th moment is controlled by `e.response.weak.estimate`; because the law is a probability
measure, the additive constant `1` in the envelope is integrable and the envelope itself is
integrable whenever its response factor is.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Integrability of the squared weak-quantity seminorm by domination.**  Let `P` be a
probability law on the coefficient space and let

`f a = besovSeminorm t (fun n z => M_0 ^ (1/2) (cellAverage U_{t-n,z} (optimizerField (c a) (u a)) - Y)) ^ 2`

be the squared scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state,
as in `e.response.weak.estimate`.  If `f` is `P`-a.e.-strongly measurable and is dominated
`P`-a.e. by an integrable function `g`, then `f` is `P`-integrable: the finite-integral half of
`Integrable` follows from `HasFiniteIntegral.mono'` after replacing `‖f a‖` by `f a` through the
nonnegativity of the square, and the measurability half is the hypothesis. -/
theorem integrable_besovSeminorm_sq_of_domination {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (g : CoeffSpace d → ℝ) (hg : Integrable g P)
    (hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P)
    (hdom : ∀ᵐ a ∂P, besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2 ≤ g a) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [hdom] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ha

/-- **Integrability of the squared weak-quantity seminorm from the recentred all-scale envelope.**
The generic domination statement with `g a = C * ((1 + respAllScaleMax P γ jStar F t a) *
respJ (respGrid jStar F) t p q' (respCoeffMinus F a) + 1)`.  The response factor
`(1 + respAllScaleMax) * respJ` is `P`-integrable by `hint` and the constant `1` is `P`-integrable
because `P` is a probability measure, so `C` times their sum is integrable and the squared
seminorm inherits integrability from the domination hypothesis. -/
theorem integrable_besovSeminorm_sq_of_ae_envelope {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P)
    (hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P)
    (hdom : ∀ᵐ a ∂P, besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2 ≤
      C * ((1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffMinus F a) + 1)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  have _ := hC
  refine integrable_besovSeminorm_sq_of_domination P jStar F t Y c u
    (fun a => C * ((1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffMinus F a) + 1)) ?_ hmeas hdom
  exact (hint.add (integrable_const (1 : ℝ))).const_mul C

/-- **Integrability of the squared weak-quantity seminorm from the adjoint all-scale envelope.**
The adjoint twin of `integrable_besovSeminorm_sq_of_ae_envelope`: the same domination argument
applies with the adjoint recentred response `respJ (respGrid jStar F) t p q' (respCoeffPlus F a)`
in place of the recentred response. -/
theorem integrable_besovSeminorm_sq_of_ae_envelope_plus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P)
    (hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P)
    (hdom : ∀ᵐ a ∂P, besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2 ≤
      C * ((1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffPlus F a) + 1)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  have _ := hC
  refine integrable_besovSeminorm_sq_of_domination P jStar F t Y c u
    (fun a => C * ((1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffPlus F a) + 1)) ?_ hmeas hdom
  exact (hint.add (integrable_const (1 : ℝ))).const_mul C

end

end Homogenization.HighContrast.Multiscale
