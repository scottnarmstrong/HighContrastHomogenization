import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportMaxBridge
import HCPoly.Entry.Multiscale.ResponseInputs.OptimizerReadoutGlue

/-!
# Measurability of the cutoff pairing in the sample

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the volume average of
the cutoff-weighted product of the gradient defect and the flux defect of the doubled optimizer
state of a response maximizer.  The doubled optimizer state of an arbitrary response maximizer is
determined almost everywhere on the response cell by the Chapter-2 canonical maximizer, by
a.e. gradient uniqueness for response maximizers (AK.HC (2.9)); the canonical selection is the one
whose cell averages depend measurably on the coefficient sample.

The reduction below is the pairing analogue of the canonical identification carried out for the
scale-average seminorm of `e.response.weak.estimate`: for each coefficient sample the two doubled
optimizer fields agree almost everywhere on the cell, so the two cutoff pairings agree, and the
measurability of the pairing transfers from the canonical coefficient family to the arbitrary family
of maximizers.  The measurability of the canonical quadratic readout itself, whose input is the
canonical coefficient object rather than the arbitrary family, is exactly the missing input recorded
as the two hypotheses `hcanonMinus` and `hcanonPlus`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing of `e.response.cutoff.estimate` is almost-everywhere strongly measurable in
the coefficient sample for an arbitrary family of response maximizers, provided the corresponding
quadratic readout of the canonical Chapter-2 optimizer state of the two recentred coefficient
families is measurable.  The arbitrary maximizer is identified with the canonical one almost
everywhere on the cell by a.e. gradient uniqueness (AK.HC (2.9)), so the pairing depends on the
sample only through the canonical selection. -/
theorem aestronglyMeasurable_abs_cutoff_pairing_of_maximizer {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (c : CoeffSpace d → CoeffField d)
    (hc : c = respCoeffMinus F ∨ c = respCoeffPlus F)
    (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a))
    (hcanonMinus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      |volumeAverage (respCell jStar F t) (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffMinusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffMinusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))|) P)
    (hcanonPlus : AEStronglyMeasurable (fun a : CoeffSpace d =>
      |volumeAverage (respCell jStar F t) (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffPlusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
        ((canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffPlusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))|) P) :
    AEStronglyMeasurable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P := by
  classical
  have _ := hφ
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hfin := Book.Ch02.Domain.instIsFiniteMeasureVolumeMeasureOn
      (adaptedDomain (respGrid jStar F) hq t)
    simpa [respCell, adaptedDomain] using hfin
  -- The canonical optimizer state only sees the a.e. class of the coefficient object.
  have hstate_aeeq : ∀ {A B : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t)},
      Book.Ch02.CoeffOn.AEEq A B → ∀ p r : Vec d,
      canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p r
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) B p r := by
    intro A B hAB p r
    have hgrad : (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) A)
          p r).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) B)
          p r).toSolution.toH1.grad := by
      simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
        (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
    filter_upwards [hgrad, hAB] with x hgradx hcoeffx
    simp only [canonicalOptimizerBlockState]
    rw [hgradx, hcoeffx]
  rcases hc with rfl | rfl
  · -- the minus recentring
    have hmain : (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffMinus F a) (u a) x).1 - Y.1)
          ((optimizerField (respCoeffMinus F a) (u a) x).2 - Y.2))|)
        = (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2))|) := by
      funext a
      congr 1
      let hv : ScalarCanonicalMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) :=
        ScalarCanonicalMaximizer.ofIsResponseMaximizer (u a) (hu a)
      obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
        exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
      have hAB : Book.Ch02.CoeffOn.AEEq (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
          (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) := by
        filter_upwards [hbf.symm] with x hx
        simpa only [canonicalRespCoeffMinusOn_toFun] using! hx
      have hstate := hstate_aeeq hAB p q'
      have hcanon := optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
        (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll hbf p q' hv
      have hfield : optimizerField (respCoeffMinus F a) (u a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)]
          canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' := by
        have hbridge : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            = canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll) p q' := rfl
        have hmid : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            =ᵐ[volumeMeasureOn (respCell jStar F t)]
            canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' := by
          rw [hbridge]
          exact hstate
        have hgrad_eq : hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad
            = (u a).toH1.grad := by
          funext x
          exact AHarmonicFunction.grad_normalizeMeanZero (u a) x
        have hnorm : optimizerField (respCoeffMinus F a) (u a)
            = optimizerField (respCoeffMinus F a)
                hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
          funext x
          simp only [optimizerField, hgrad_eq]
        rw [hnorm]
        exact hcanon.symm.trans hmid
      unfold volumeAverage
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hfield] with x hx
      rw [hx]
    rw [hmain]
    exact hcanonMinus
  · -- the plus recentring
    have hmain : (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (respCoeffPlus F a) (u a) x).1 - Y.1)
          ((optimizerField (respCoeffPlus F a) (u a) x).2 - Y.2))|)
        = (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2))|) := by
      funext a
      congr 1
      let hv : ScalarCanonicalMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) :=
        ScalarCanonicalMaximizer.ofIsResponseMaximizer (u a) (hu a)
      obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
        exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
      have hAB : Book.Ch02.CoeffOn.AEEq (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
          (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) := by
        filter_upwards [hbf.symm] with x hx
        simpa only [canonicalRespCoeffPlusOn_toFun] using! hx
      have hstate := hstate_aeeq hAB p q'
      have hcanon := optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
        (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll hbf p q' hv
      have hfield : optimizerField (respCoeffPlus F a) (u a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)]
          canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' := by
        have hbridge : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            = canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll) p q' := rfl
        have hmid : optimizerField f
              (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll)
                p q')
            =ᵐ[volumeMeasureOn (respCell jStar F t)]
            canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' := by
          rw [hbridge]
          exact hstate
        have hgrad_eq : hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad
            = (u a).toH1.grad := by
          funext x
          exact AHarmonicFunction.grad_normalizeMeanZero (u a) x
        have hnorm : optimizerField (respCoeffPlus F a) (u a)
            = optimizerField (respCoeffPlus F a)
                hv.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
          funext x
          simp only [optimizerField, hgrad_eq]
        rw [hnorm]
        exact hcanon.symm.trans hmid
      unfold volumeAverage
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hfield] with x hx
      rw [hx]
    rw [hmain]
    exact hcanonPlus

end

end Homogenization.HighContrast.Multiscale
