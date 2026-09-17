import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCanonAvg
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCanRead
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPairingMeasFamily
import HCPoly.Entry.Multiscale.ResponseInputs.MaximizerSelection

/-!
# Weighted averages of the doubled optimizer field are measurable in the sample

The doubled optimizer field of a response maximizer for the recentred coefficients `a_-` and `a_+`
is determined, up to a null set of the response cell, by the coefficient sample alone: Chapter-2
almost-everywhere gradient uniqueness identifies every response maximizer with the canonical
selection.  Consequently every cutoff-weighted average of a coordinate of the doubled optimizer
field over a measurable subcell is a measurable function of the sample, for an arbitrary family of
maximizers.  This is the linear companion of the weighted energy readout: it gives the
sample-measurability of the cutoff-weighted state mean entering the weak quantity of
`e.response.weak.estimate`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The canonical doubled optimizer state depends on the coefficient only through its
almost-everywhere class on the domain. -/
private theorem canonicalOptimizerBlockState_congr_ae {d : ℕ} {U : Book.Ch02.Domain d}
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
theorem optimizerField_ae_eq_canonicalState_respCoeffMinus {d : ℕ} [NeZero d]
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
    simpa [volumeMeasureOn] using (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
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
    canonicalOptimizerBlockState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- An arbitrary response maximizer for the recentred coefficient `a_+` on an invertible adapted
cell has the same doubled optimizer field almost everywhere as the canonical Chapter-2 selection. -/
theorem optimizerField_ae_eq_canonicalState_respCoeffPlus {d : ℕ} [NeZero d]
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
    simpa [volumeMeasureOn] using (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
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
    canonicalOptimizerBlockState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- Every cutoff-weighted average of a coordinate of the doubled optimizer field of an arbitrary
family of response maximizers for the recentred coefficient `a_-` is measurable in the coefficient
sample.  The field need not be measurable in the sample, but its weighted average is determined by
the measurable canonical selection through Chapter-2 a.e. gradient uniqueness, so the weighted
subcell mean entering the weak quantity of `e.response.weak.estimate` is measurable. -/
theorem measurable_volumeAverage_weighted_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) alpha) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) alpha))
      = fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
          toFullBlockVec (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x) alpha) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffMinus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (uM a) (hmax a)
    have hInt : (fun x => eta x *
          toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) alpha)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * toFullBlockVec (canonicalOptimizerBlockState
          (adaptedDomain (respGrid jStar F) hq t)
          (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x) alpha) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffMinus F a) (uM a) x = _ from hx]
    exact volumeAverage_congr_ae hVU hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_canonicalRespCoeffMinus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) alpha hV hVU heta

/-- Every cutoff-weighted average of a coordinate of the doubled optimizer field of an arbitrary
family of response maximizers for the recentred coefficient `a_+` is measurable in the coefficient
sample.  This is the plus twin of
`measurable_volumeAverage_weighted_optimizerField_respCoeffMinus`. -/
theorem measurable_volumeAverage_weighted_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) alpha) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) alpha))
      = fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
          toFullBlockVec (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x) alpha) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffPlus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (uP a) (hmax a)
    have hInt : (fun x => eta x *
          toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) alpha)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * toFullBlockVec (canonicalOptimizerBlockState
          (adaptedDomain (respGrid jStar F) hq t)
          (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x) alpha) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffPlus F a) (uP a) x = _ from hx]
    exact volumeAverage_congr_ae hVU hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_canonicalRespCoeffPlus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) alpha hV hVU heta

end

end Homogenization.HighContrast.Multiscale
