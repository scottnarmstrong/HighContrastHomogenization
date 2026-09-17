import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPairMeas
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCanPairMeas

/-!
# Measurability of the cutoff pairing for an arbitrary maximizer family

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the volume average,
over the response cell `U_t`, of the cutoff-weighted Euclidean pairing of the potential defect and
the flux defect of the doubled optimizer state of a response maximizer.  This file records that the
absolute value of that pairing is almost-everywhere strongly measurable in the coefficient
sample for an arbitrary family of response maximizers.

The doubled optimizer state of an arbitrary response maximizer agrees almost everywhere on the
response cell with the Chapter-2 canonical maximizer, by a.e. gradient uniqueness for response
maximizers (AK.HC (2.9)); the pairing therefore agrees almost everywhere with the canonical pairing.
The canonical pairing is then reduced to its genuinely quadratic term by the pointwise expansion of
the integrand, whose three remaining linear readouts of the canonical optimizer state are
measurable.  Only that quadratic canonical readout is carried as an explicit hypothesis, in the two
recentrings of `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)).
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A volume average over a set `V` is unchanged by an almost-everywhere equality of the integrand
on a larger set `U ⊇ V`.  This is the scalar analogue of `cellAverage_congr_ae`. -/
theorem volumeAverage_congr_ae {d : ℕ} {V U : Set (Vec d)} (hVU : V ⊆ U)
    {f g : Vec d → ℝ} (h : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage V f = volumeAverage V g := by
  have h2 : f =ᵐ[volumeMeasureOn V] g :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae h2

/-- The absolute value of the cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is almost-everywhere strongly measurable in the coefficient sample for an
arbitrary family of response maximizers of the two recentred response coefficient families, provided
the cutoff-weighted volume average of the quadratic self-pairing of the canonical Chapter-2 optimizer
state is measurable in each case.

The arbitrary maximizer is identified with the canonical one almost everywhere on the response cell
by a.e. gradient uniqueness for response maximizers (AK.HC (2.9)), so the pairing depends on the
sample only through the canonically selected optimizer state.  The canonical pairing is expanded
into its quadratic term and the three linear readouts whose measurability is recorded in
`aestronglyMeasurable_abs_canonical_cutoff_pairing_minus_of_quadratic` and its plus twin. -/
theorem aestronglyMeasurable_abs_pairing_of_maximizer {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (c : CoeffSpace d → CoeffField d)
    (hc : c = respCoeffMinus F ∨ c = respCoeffPlus F)
    (p q' : Vec d) (Y : BlockVec d) {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a))
    (hquadMinus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell (respGrid jStar F) t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffMinusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffMinusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2)) P)
    (hquadPlus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell (respGrid jStar F) t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffPlusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1
        (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t)
          (canonicalRespCoeffPlusOn (respGrid jStar F)
            (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2)) P) :
    AEStronglyMeasurable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P := by
  refine aestronglyMeasurable_abs_cutoff_pairing_of_maximizer
    P jStar F t hjStar hm φ hφ c hc p q' Y u hu ?_ ?_
  · simpa only [respCell] using
      aestronglyMeasurable_abs_canonical_cutoff_pairing_minus_of_quadratic
        P jStar F t hjStar hm φ hφ p q' Y hquadMinus
  · simpa only [respCell] using
      aestronglyMeasurable_abs_canonical_cutoff_pairing_plus_of_quadratic
        P jStar F t hjStar hm φ hφ p q' Y hquadPlus

end

end Homogenization.HighContrast.Multiscale
