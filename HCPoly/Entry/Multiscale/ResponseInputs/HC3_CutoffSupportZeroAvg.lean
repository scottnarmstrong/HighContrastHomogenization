import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportIBP

/-!
# Vanishing of a solenoidal field against a cutoff gradient

Testing the weak solenoidal condition `Homogenization.IsSolenoidalOn` on a smooth compactly
supported function `φ` whose support lies in the open bounded convex domain `U` shows that the
pairing of the field with the gradient of `φ` integrates to zero.  A smooth compactly supported
function supported in `U` is an `H¹₀(U)` test function, so the weak divergence-free condition
applies to it directly, and its gradient is the Fréchet derivative.

Consequently the normalized volume average of the same pairing vanishes as well.  This is the
observation that lets the cutoff argument behind `e.response.cutoff.estimate` replace a potential
by its centred version at no cost: the difference produced by centring is a constant multiple of
this average.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A weakly divergence-free field pairs to zero against the gradient of a smooth compactly
supported cutoff whose support lies in the domain.  For an open bounded convex domain `U`, a field
`g` satisfying `IsSolenoidalOn U g`, and a smooth `φ` with compact support contained in `U`, the
integral over `U` of the pairing of `g` with the gradient `fun j => (fderiv ℝ φ x) (basisVec j)`
is zero.  This is the vanishing used in the cutoff argument `e.response.cutoff.estimate`. -/
theorem integral_vecDot_solenoidal_gradCutoff_eq_zero {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {g : Vec d → Vec d} (hsol : IsSolenoidalOn U g)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U) :
    (∫ x in U, vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) = 0 :=
  hsol.test_of_contDiff hU.isOpen hφ hφ_compact hφ_sub

/-- The normalized volume average of a weakly divergence-free field against the gradient of a
smooth compactly supported cutoff vanishes.  For an open bounded convex domain `U`, a field `g`
satisfying `IsSolenoidalOn U g`, and a smooth `φ` with compact support contained in `U`, the
volume average over `U` of the pairing of `g` with `fun j => (fderiv ℝ φ x) (basisVec j)` is zero.
This is the vanishing used in the cutoff argument `e.response.cutoff.estimate`. -/
theorem volumeAverage_vecDot_solenoidal_gradCutoff_eq_zero {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {g : Vec d → Vec d} (hsol : IsSolenoidalOn U g)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U) :
    volumeAverage U (fun x => vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) = 0 :=
  volumeAverage_eq_zero_of_integral_eq_zero
    (integral_vecDot_solenoidal_gradCutoff_eq_zero hU hsol hφ hφ_compact hφ_sub)

end

end Homogenization.HighContrast.Multiscale
