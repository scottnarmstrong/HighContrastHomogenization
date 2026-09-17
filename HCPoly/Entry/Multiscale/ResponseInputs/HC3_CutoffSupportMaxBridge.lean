import HCPoly.Entry.Multiscale.ResponseInputs.MaximizerSelection

/-!
# Cell averages of an arbitrary response maximizer and the canonical selection

For a coefficient field `b` that agrees almost everywhere on a Chapter-2 domain `U` with a field
`f` that is uniformly elliptic there, every response maximizer for the loads `p`, `q` has the
subcell averages of the doubled optimizer state of the Chapter-2 canonical maximizer for `f`.

The argument is that a response maximizer may be normalized to have mean zero without changing its
gradient, so it is a scalar canonical maximizer; Chapter-2 a.e. gradient uniqueness for response
maximizers (AK.HC (2.9)) then identifies its doubled optimizer state with that of the canonical
choice.  This is the step that makes the doubled optimizer state `X_t^\pm` entering the weak
quantity `W^\pm` of `e.response.weak.estimate` a function of the sample through the measurable
canonical selection alone, independently of the choice of maximizer.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- If `b` agrees almost everywhere on a Chapter-2 domain `U` with a field `f` that is uniformly
elliptic on `U`, then the cell average over any `V ⊆ U` of the doubled optimizer state of an
arbitrary response maximizer of the response functional for loads `p`, `q` equals the cell average
of the doubled optimizer state of the Chapter-2 canonical maximizer for `f`.

A response maximizer may be normalized to have mean zero without changing its gradient, so it
becomes a scalar canonical maximizer; Chapter-2 a.e. gradient uniqueness for response maximizers
(AK.HC (2.9)) then identifies its doubled optimizer state with that of the canonical choice.  This
is the form in which the doubled optimizer state `X_t^\pm` entering the weak quantity `W^\pm` of
`e.response.weak.estimate` is seen to be determined by the measurable canonical selection,
independently of the choice of maximizer. -/
theorem cellAverage_optimizerField_eq_canonical {d : ℕ} {U : Book.Ch02.Domain d}
    {V : Set (Vec d)} (hVU : V ⊆ (U : Set (Vec d)))
    {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (hbf : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (u : AHarmonicFunction b (U : Set (Vec d)))
    (hu : IsResponseMaximizer (U : Set (Vec d)) p q b u) :
    cellAverage V (optimizerField b u)
      = cellAverage V (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q)) := by
  classical
  let v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hcanon : cellAverage V
        (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q)) =
      cellAverage V (optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) :=
    cellAverage_scalarCanonicalMaximizer_eq_canonicalOfAEEq hVU hlam hle hEll hbf p q v
  have hgrad :
      v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad = u.toH1.grad := by
    funext x
    exact AHarmonicFunction.grad_normalizeMeanZero u x
  have hfield : ∀ x, optimizerField b u x
      = optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction x := by
    intro x
    simp only [optimizerField, hgrad]
  have htransport : cellAverage V (optimizerField b u)
      = cellAverage V (optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) :=
    cellAverage_congr_ae hVU (Filter.Eventually.of_forall hfield)
  exact htransport.trans hcanon.symm

end

end Homogenization.HighContrast.Multiscale
