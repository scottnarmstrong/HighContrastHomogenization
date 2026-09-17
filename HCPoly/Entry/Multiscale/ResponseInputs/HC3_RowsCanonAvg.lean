import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCanRead
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportMaxBridge
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# Cell averages of the doubled optimizer field are measurable in the sample

The doubled optimizer field of a response maximizer for the recentred coefficients `a_-` and
`a_+` is determined, up to a null set of the response cell, by the coefficient sample alone:
Chapter-2 almost-everywhere gradient uniqueness identifies every response maximizer with the
canonical selection.  Consequently every coordinate of the cell average of the doubled optimizer
field over a measurable subcell is a measurable function of the sample, for an arbitrary family of
maximizers.  These are the subcell averages entering the weak quantity of
`e.response.weak.estimate`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The full block vector of a cell average is the volume average of the full block vector of the
field. -/
private theorem toFullBlockVec_cellAverage {d : ℕ} (V : Set (Vec d)) (X : Vec d → BlockVec d)
    (alpha : BlockCoord d) :
    toFullBlockVec (cellAverage V X) alpha =
      volumeAverage V (fun x => toFullBlockVec (X x) alpha) := by
  cases alpha <;> rfl

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

/-- The cell average of the doubled optimizer field of an arbitrary response maximizer for a
coefficient agreeing almost everywhere with an elliptic field equals the cell average of the
canonical doubled optimizer state for that field. -/
private theorem cellAverage_optimizerField_eq_canonicalBlockState {d : ℕ}
    {U : Book.Ch02.Domain d} {V : Set (Vec d)} (hVU : V ⊆ (U : Set (Vec d)))
    {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (hbf : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (u : AHarmonicFunction b (U : Set (Vec d)))
    (hu : IsResponseMaximizer (U : Set (Vec d)) p q b u)
    (aU : Book.Ch02.CoeffOn U)
    (hA : Book.Ch02.CoeffOn.AEEq (coeffOnOfIsEllipticFieldOn (U := U) hlam hle hEll) aU) :
    cellAverage V (optimizerField b u)
      = cellAverage V (canonicalOptimizerBlockState U aU p q) := by
  calc cellAverage V (optimizerField b u)
      = cellAverage V (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn
            (coeffOnOfIsEllipticFieldOn (U := U) hlam hle hEll) p q)) :=
        cellAverage_optimizerField_eq_canonical (U := U) hVU hlam hle hEll hbf p q u hu
    _ = cellAverage V (canonicalOptimizerBlockState U
          (coeffOnOfIsEllipticFieldOn (U := U) hlam hle hEll) p q) := by
        apply congrArg (cellAverage V)
        funext x
        rfl
    _ = cellAverage V (canonicalOptimizerBlockState U aU p q) :=
        cellAverage_congr_ae hVU (canonicalOptimizerBlockState_congr_ae hA p q)

/-- The minus bridge at an invertible grid: the cell average of the doubled optimizer field of an
arbitrary response maximizer for `a_-` equals the cell average of the canonical state for `a_-`. -/
private theorem cellAverage_optimizerField_respCoeffMinus_eq_canonical {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u)
    {V : Set (Vec d)} (hVU : V ⊆ HighContrast.adaptedCell q t) :
    cellAverage V (optimizerField (respCoeffMinus F a) u)
      = cellAverage V (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact cellAverage_optimizerField_eq_canonicalBlockState (U := adaptedDomain q hq t)
    hVU hlam hle hEll hbf p r u hu (canonicalRespCoeffMinusOn q hq t F a) (by
      filter_upwards [hbf.symm] with x hx
      simpa only [canonicalRespCoeffMinusOn_toFun] using! hx)

/-- The plus bridge at an invertible grid: the cell average of the doubled optimizer field of an
arbitrary response maximizer for `a_+` equals the cell average of the canonical state for `a_+`. -/
private theorem cellAverage_optimizerField_respCoeffPlus_eq_canonical {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u)
    {V : Set (Vec d)} (hVU : V ⊆ HighContrast.adaptedCell q t) :
    cellAverage V (optimizerField (respCoeffPlus F a) u)
      = cellAverage V (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact cellAverage_optimizerField_eq_canonicalBlockState (U := adaptedDomain q hq t)
    hVU hlam hle hEll hbf p r u hu (canonicalRespCoeffPlusOn q hq t F a) (by
      filter_upwards [hbf.symm] with x hx
      simpa only [canonicalRespCoeffPlusOn_toFun] using! hx)

/-- Each coordinate of the cell average of the doubled optimizer field of an arbitrary family of
response maximizers for the recentred coefficient `a_-` is measurable in the coefficient sample.
The field need not be measurable in the sample, but its cell average is determined by the
measurable canonical selection through Chapter-2 a.e. gradient uniqueness, so the subcell average
entering the weak quantity of `e.response.weak.estimate` is measurable. -/
theorem measurable_cellAverage_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffMinus F a) (uM a))) alpha := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffMinus F a) (uM a))) alpha)
      = fun a : CoeffSpace d => volumeAverage V (fun x => toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x) alpha) := by
    funext a
    rw [show cellAverage V (optimizerField (respCoeffMinus F a) (uM a)) = _ from
      cellAverage_optimizerField_respCoeffMinus_eq_canonical (q := respGrid jStar F) hq t F a
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a) (hmax a) hVU]
    rw [toFullBlockVec_cellAverage]
  rw [hEq]
  exact measurable_cellAverage_canonicalRespCoeffMinus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) alpha hV hVU

/-- Each coordinate of the cell average of the doubled optimizer field of an arbitrary family of
response maximizers for the recentred coefficient `a_+` is measurable in the coefficient sample.
This is the plus twin of `measurable_cellAverage_optimizerField_respCoeffMinus`. -/
theorem measurable_cellAverage_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d) (alpha : BlockCoord d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffPlus F a) (uP a))) alpha := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
      toFullBlockVec (cellAverage V (optimizerField (respCoeffPlus F a) (uP a))) alpha)
      = fun a : CoeffSpace d => volumeAverage V (fun x => toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x) alpha) := by
    funext a
    rw [show cellAverage V (optimizerField (respCoeffPlus F a) (uP a)) = _ from
      cellAverage_optimizerField_respCoeffPlus_eq_canonical (q := respGrid jStar F) hq t F a
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a) (hmax a) hVU]
    rw [toFullBlockVec_cellAverage]
  rw [hEq]
  exact measurable_cellAverage_canonicalRespCoeffPlus (respGrid jStar F) hq t F
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) alpha hV hVU

end

end Homogenization.HighContrast.Multiscale
