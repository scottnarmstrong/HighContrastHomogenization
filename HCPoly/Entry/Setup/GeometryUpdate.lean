import HCPoly.Entry.Setup.ProjectiveDistance
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HCPoly.Setup.TransportObjects

/-!
# The geometry update `𝔪_+`

`e.renormalization.geometry.update`:

> For the following geometry update, write `𝔪_* := m(𝐀hom_{n+2L,q})` and set
> `𝔪_+ := 𝔪^{1/2}(𝔪^{-1/2}𝔪_*𝔪^{-1/2})^{min{ε/d_pr([𝔪],[𝔪_*]),1}}𝔪^{1/2}` if `[𝔪] ≠ [𝔪_*]`,
> and `𝔪_+ := 𝔪_*` if `[𝔪] = [𝔪_*]`.

The update is a function of `ε`, `𝔪` and `𝔪_*`; the print's `𝔪_* = m(𝐀hom_{n+2L,q})` is the
argument a consumer supplies, and is not built in.

The case split is the printed one, on the equality of the projective classes
(`ProjectiveEq` of `HCPoly/Entry/Setup/ProjectiveDistance.lean`), decided classically.  On the branch
where the classes differ, the exponent is `min{ε/d_pr([𝔪],[𝔪_*]), 1}` as printed; that
`d_pr([𝔪],[𝔪_*]) ≠ 0` there — so that the quotient is not Lean's `x / 0 = 0` — is exactly
the statement that `d_pr` separates distinct classes.  That separation is not definitional;
the printed display is followed as written rather than repaired to make it so.

The fractional power `A^θ` is the continuous functional calculus of `x ↦ x^θ` (real
`rpow`).  On positive matrices it is the printed power; elsewhere it uses Mathlib's total
real-power/CFC conventions, including the CFC fallback when its own conditions fail.

The guard here is the printed one, on `[𝔪] = [𝔪_*]`.  An alternative guard splitting on the
vanishing of the projective distance agrees with it exactly when `d_pr` separates distinct
classes — the same fact the printed display needs — and the printed guard is the one written
here.
-/

open Homogenization.HighContrast (matPow matSqrt)
namespace Homogenization.HighContrast

noncomputable section

variable {d : ℕ}

open Classical in
/-- The geometry update `𝔪_+` of `e.renormalization.geometry.update`:
`𝔪^{1/2}(𝔪^{-1/2}𝔪_*𝔪^{-1/2})^{min{ε/d_pr([𝔪],[𝔪_*]),1}}𝔪^{1/2}` when the projective classes
differ, and `𝔪_*` when they agree. -/
def geometryUpdate (ε : ℝ) (m mStar : Mat d) : Mat d :=
  if ProjectiveEq m mStar then mStar
  else
    matSqrt m *
        matPow (min (ε / projectiveDistance m mStar) 1) (normalizedMat m mStar) *
      matSqrt m

end

end Homogenization.HighContrast
