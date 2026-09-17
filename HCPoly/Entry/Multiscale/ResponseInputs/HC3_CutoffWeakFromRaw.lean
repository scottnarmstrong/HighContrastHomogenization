import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportMeasFamily
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffWeakDomination
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffEnvelopeIntegrable
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffWeakIntegrable
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportQuadMeasB
import HCPoly.Entry.Multiscale.SelectionExponentBounds

/-!
# Integrability of the weak-quantity integrand from the standing law premises

The weak quantity `W^\pm` of `e.response.weak.estimate` is the sample expectation of the square of
the scale-average seminorm `besovSeminorm` of the recentred, canonically-metric-scaled cell averages
of the doubled optimizer state `X_t^\pm`, for an arbitrary family of response maximizers.  This file
assembles the three landed ingredients into the integrability of that integrand, starting from the
standing law premises `IsStationaryLaw` and the coarse-ellipticity dagger.

The ingredients are:

* almost-everywhere strong measurability of the integrand, from the measurable canonical selection
  and the countable sum defining the seminorm;
* almost-sure domination of the integrand by a constant multiple of the all-scale envelope
  `(1 + respAllScaleMax) * respJ + 1`, from the pathwise scale-average seminorm bound AK.HC (2.130)
  and the energy--response identity of `e.response.weak.estimate`;
* integrability of that envelope, from the `Q`-th envelope moment with `2 ≤ Q` supplied by
  `e.response.weak.estimate` and Hölder's inequality, together with the elementary domination
  argument closing the square.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Integrability of the squared weak-quantity seminorm from the standing law premises, recentred
sign.**  Let `P` be a stationary probability law with coarse-ellipticity dagger, let `F` be a block
with positive-definite canonical metric, and let `u` be an arbitrary family of response maximizers
for the recentred coefficient `a_-`.  Assume the all-scale envelope `ℳ = respAllScaleMax` is
measurable with `Q`-th moment `P`-integrable and `J^- ^ 2` is `P`-integrable.  Then the squared
scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state is `P`-integrable.
This is the integrability of the integrand of the weak quantity `W^-` of
`e.response.weak.estimate`; the a.e. domination is supplied by AK.HC (2.130) and the closing
domination argument by Hölder. -/
theorem integrable_besovSeminorm_sq_of_raw_minus {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hJsq : Integrable (fun a =>
      respJ (respGrid jStar F) t p q' (respCoeffMinus F a) ^ 2) P)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) (u a)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P :=
    (measurable_respJ_respCoeffMinus (respGrid jStar F) hq t F p q').aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2) P :=
    aestronglyMeasurable_besovSeminorm_sq_of_maximizer P jStar F t hj hm
      (respCoeffMinus F) (Or.inl rfl) p q' Y u hu
  have hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P :=
    integrable_one_add_respAllScaleMax_mul_respJ hd γ hγ P jStar F t p q'
      hMmeas hMint (bigQ_two_le d hd γ hγ) hJsq hJmeas
  obtain ⟨C, hC, hdom⟩ := ae_besovSeminorm_sq_le_envelope_minus hd γ hγ P E Ψ Kg Src
    hstat hdag jStar hj F hm t p q' Y u hu
  exact integrable_besovSeminorm_sq_of_ae_envelope P γ jStar F t p q' Y
    (respCoeffMinus F) u C hC hmeas hint hdom

/-- **Integrability of the squared weak-quantity seminorm from the standing law premises, adjoint
sign.**  The adjoint twin of `integrable_besovSeminorm_sq_of_raw_minus`: with the adjoint recentred
coefficient `a_+` and an arbitrary family `u` of response maximizers for it, the same hypotheses on
the all-scale envelope and on `J^+ ^ 2` give `P`-integrability of the squared scale-average seminorm
of the `M_0 ^ (1/2)`-transported adjoint optimizer state.  This is the integrability of the
integrand of the weak quantity `W^+` of `e.response.weak.estimate`. -/
theorem integrable_besovSeminorm_sq_of_raw_plus {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hJsq : Integrable (fun a =>
      respJ (respGrid jStar F) t p q' (respCoeffPlus F a) ^ 2) P)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) (u a)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P :=
    (measurable_respJ_respCoeffPlus (respGrid jStar F) hq t F p q').aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2) P :=
    aestronglyMeasurable_besovSeminorm_sq_of_maximizer P jStar F t hj hm
      (respCoeffPlus F) (Or.inr rfl) p q' Y u hu
  have hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P :=
    integrable_one_add_respAllScaleMax_mul_respJPlus hd γ hγ P jStar F t p q'
      hMmeas hMint (bigQ_two_le d hd γ hγ) hJsq hJmeas
  obtain ⟨C, hC, hdom⟩ := ae_besovSeminorm_sq_le_envelope_plus hd γ hγ P E Ψ Kg Src
    hstat hdag jStar hj F hm t p q' Y u hu
  exact integrable_besovSeminorm_sq_of_ae_envelope_plus P γ jStar F t p q' Y
    (respCoeffPlus F) u C hC hmeas hint hdom

end

end Homogenization.HighContrast.Multiscale
