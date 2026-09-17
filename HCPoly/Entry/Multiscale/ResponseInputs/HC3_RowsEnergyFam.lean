import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffQuadConnectTwo
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportMeasFamily
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPairingMeasFamily

/-!
# The weighted optimizer energy is measurable in the sample

Two response maximizers for the same loads and the same coefficient have the same doubled optimizer
field almost everywhere on the response cell, by Chapter-2 almost-everywhere gradient uniqueness
(AK.HC (2.9)).  Hence every weighted average of the energy density of the terminal optimizer of
`p.response.transfer` is computed by the canonical Chapter-2 selection, which depends measurably on
the sample.  In particular the `(φ - 1)`-weighted terminal energy and the energy on each aligned
subcell are measurable functions of the sample, for an arbitrary family of maximizers.

The pointwise pairing of the doubled optimizer field with itself is the variation energy
`∇v · (symmPart b) ∇v`: the antisymmetric part of the coefficient contributes nothing to the
quadratic form, so the pairing may be read with either the full coefficient or its symmetric part.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The canonical doubled optimizer state depends on the coefficient only through its
almost-everywhere class on the domain. -/
private theorem energyCanonicalState_congr_ae {d : ℕ} {U : Book.Ch02.Domain d}
    {A B : Book.Ch02.CoeffOn U} (hAB : Book.Ch02.CoeffOn.AEEq A B) (p r : Vec d) :
    canonicalOptimizerBlockState U A p r
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] canonicalOptimizerBlockState U B p r := by
  have hgrad : (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U A) p r).toSolution.toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U B) p r).toSolution.toH1.grad := by
    simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
      (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
  filter_upwards [hgrad, hAB] with x hgradx hcoeffx
  simp only [canonicalOptimizerBlockState]
  rw [hgradx, hcoeffx]

/-- An arbitrary response maximizer for the recentred coefficient `a_-` on an invertible adapted
cell has the same doubled optimizer field almost everywhere as the canonical Chapter-2 selection. -/
private theorem optimizerField_aeeq_canonicalRespCoeffMinus {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    optimizerField (respCoeffMinus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using
      (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  let A : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
    coeffOnOfIsEllipticFieldOn (U := adaptedDomain q hq t) hlam hle hEll
  let v : ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hgrad : optimizerField (respCoeffMinus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffMinus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    apply Filter.Eventually.of_forall
    intro x
    have hg : v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad x
        = u.toH1.grad x := AHarmonicFunction.grad_normalizeMeanZero u x
    simp only [optimizerField, hg]
  have hcanon : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffMinus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        = optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) := by
      funext x
      rfl
    have hstateEq : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) :=
      Filter.Eventually.of_forall (fun x => congrFun hstate x)
    exact hstateEq.trans (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      (U := adaptedDomain q hq t) hlam hle hEll hbf p r v)
  have hAB : Book.Ch02.CoeffOn.AEEq A (canonicalRespCoeffMinusOn q hq t F a) := by
    filter_upwards [hbf.symm] with x hx
    simpa only [canonicalRespCoeffMinusOn_toFun] using! hx
  have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r :=
    energyCanonicalState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- An arbitrary response maximizer for the recentred coefficient `a_+` on an invertible adapted
cell has the same doubled optimizer field almost everywhere as the canonical Chapter-2 selection. -/
private theorem optimizerField_aeeq_canonicalRespCoeffPlus {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    optimizerField (respCoeffPlus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using
      (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  let A : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
    coeffOnOfIsEllipticFieldOn (U := adaptedDomain q hq t) hlam hle hEll
  let v : ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hgrad : optimizerField (respCoeffPlus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffPlus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    apply Filter.Eventually.of_forall
    intro x
    have hg : v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad x
        = u.toH1.grad x := AHarmonicFunction.grad_normalizeMeanZero u x
    simp only [optimizerField, hg]
  have hcanon : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffPlus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        = optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) := by
      funext x
      rfl
    have hstateEq : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) :=
      Filter.Eventually.of_forall (fun x => congrFun hstate x)
    exact hstateEq.trans (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      (U := adaptedDomain q hq t) hlam hle hEll hbf p r v)
  have hAB : Book.Ch02.CoeffOn.AEEq A (canonicalRespCoeffPlusOn q hq t F a) := by
    filter_upwards [hbf.symm] with x hx
    simpa only [canonicalRespCoeffPlusOn_toFun] using! hx
  have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r :=
    energyCanonicalState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- The `η`-weighted terminal optimizer energy of the response functional for the recentred
coefficient `a_-`, for an arbitrary family of response maximizers, is measurable in the coefficient
sample.  The energy is the pairing `⟨X.1, X.2⟩ = ∇v · a_- ∇v` of the doubled optimizer field of the
maximizer; that field is determined almost everywhere by the measurable canonical Chapter-2
selection, so the weighted energy is a measurable function of the sample. -/
theorem measurable_volumeAverage_weighted_energy_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {eta : Vec d → ℝ}
    (hetam : MeasureTheory.AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)))
    (hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).2) := by
    funext a
    have hfield := optimizerField_aeeq_canonicalRespCoeffMinus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (uM a) (hmax a)
    have hInt : (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).2) := by
      filter_upwards [hfield] with x hfieldx
      show eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x
          = eta x * vecDot
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).1
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).2
      have hpt : scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x
          = vecDot
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffMinus F a) (uM a) x).1
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffMinus F a) (uM a) x).2 := by
        simp only [scalarVariationEnergyIntegrand, optimizerField]
        exact vecDot_matVecMul_symmPart (respCoeffMinus F a x) ((uM a).toH1.grad x)
      rw [hpt, hfieldx]
    exact volumeAverage_congr_ae subset_rfl hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_quadratic_canonicalRespCoeffMinus
    (respGrid jStar F) hq t F (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
    hetam hetab

/-- The `η`-weighted terminal optimizer energy of the response functional for the adjoint
coefficient `a_+`, for an arbitrary family of response maximizers, is measurable in the coefficient
sample.  This is the adjoint twin of `measurable_volumeAverage_weighted_energy_respCoeffMinus`. -/
theorem measurable_volumeAverage_weighted_energy_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {eta : Vec d → ℝ}
    (hetam : MeasureTheory.AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)))
    (hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).2) := by
    funext a
    have hfield := optimizerField_aeeq_canonicalRespCoeffPlus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (uP a) (hmax a)
    have hInt : (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).2) := by
      filter_upwards [hfield] with x hfieldx
      show eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x
          = eta x * vecDot
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).1
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).2
      have hpt : scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x
          = vecDot
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffPlus F a) (uP a) x).1
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffPlus F a) (uP a) x).2 := by
        simp only [scalarVariationEnergyIntegrand, optimizerField]
        exact vecDot_matVecMul_symmPart (respCoeffPlus F a x) ((uP a).toH1.grad x)
      rw [hpt, hfieldx]
    exact volumeAverage_congr_ae subset_rfl hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_quadratic_canonicalRespCoeffPlus
    (respGrid jStar F) hq t F (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
    hetam hetab

end

end Homogenization.HighContrast.Multiscale
