import HCPoly.Setup.BlockAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The projective distance `d_pr([𝔪_0],[𝔪_1])`

Near `e.scale.selection.projective.distance`:

> For positive `d`-by-`d` matrices `𝔪_0, 𝔪_1`, define
> `d_pr([𝔪_0],[𝔪_1]) := ½ log (λ_max(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}) / λ_min(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}))`.

The extreme eigenvalues are written in their Loewner forms, which is how the setup layer
already writes `λ_max`: `specBound M` of `HCPoly/Setup/BlockAlgebra.lean` is
`inf {t ≥ 0 : M ≤ tI}`, the largest eigenvalue of a symmetric positive semidefinite `M`, and
`specMin` below is the dual `sup {t : tI ≤ M}`.  No matrix square root and no eigenvalue
family enters a scalar quantity; that convention is the setup layer's, not this file's.

Three things are recorded because a reader comparing this file to the manuscript would
otherwise have to reconstruct them (operating rules, the standing honesty rule):

* The printed argument is the projective **class** `[𝔪]`, and the function here takes
  representatives.  That `d_pr` depends only on the classes — it is invariant under
  `𝔪_i ↦ c 𝔪_i` with `c > 0` — is a statement about the value and is proved, not definitional.
  The class itself is rendered as the relation `ProjectiveEq`, which is what the case split
  of the geometry update `e.renormalization.geometry.update` tests.
* The printed hypothesis "positive `𝔪_0, 𝔪_1`" is not part of the definition.  Off the
  positive matrices, `𝔪_0⁻¹` and its square root take the junk values of
  `HCPoly/Setup/BlockAlgebra.lean`, `specMin` of a matrix with an empty lower-threshold set is
  totalized by `sSup`, and `log` of a nonpositive quotient is Mathlib's junk `log`.
* The quotient is written as printed, `λ_max / λ_min`, not as the product
  `λ_max(X) · λ_max(X⁻¹)`; the two agree on positive `X`, but only the first is the display.

An alternative definition writes the distance through the two relative sizes,
`½(log relSize(𝔪_1,𝔪_0) + log relSize(𝔪_0,𝔪_1))`, and proves the printed form as a
theorem (`projDist_eq_norm_form`).  That shape is **not** adopted: it is the printed display
only after that theorem, and a definition may not embed a proved identity.  The `d`-by-`d`
normalization `𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}` is the analogue of `normalizedBlock`, and that shape
is adopted.
-/

open Homogenization.HighContrast (matSqrt specBound)
namespace Homogenization.HighContrast

noncomputable section

variable {d : ℕ}

/-- The smallest eigenvalue of a symmetric matrix, in Loewner form: `sup {t : t I ≤ M}`.
This is the dual of `specBound`, which is `inf {t ≥ 0 : M ≤ t I}`. -/
def specMin (M : Mat d) : ℝ :=
  sSup {t : ℝ | MatLoewnerLE (t • (1 : Mat d)) M}

/-- The normalized matrix `𝔪_0^{-1/2} 𝔪_1 𝔪_0^{-1/2}`, the root being the canonical
positive semidefinite square root of `𝔪_0⁻¹`. -/
def normalizedMat (m₀ m₁ : Mat d) : Mat d :=
  matSqrt m₀⁻¹ * m₁ * matSqrt m₀⁻¹

/-- The projective class relation `[𝔪_0] = [𝔪_1]`: the two matrices differ by a positive
scalar.  This is the case distinction the geometry update `e.renormalization.geometry.update` makes. -/
def ProjectiveEq (m₀ m₁ : Mat d) : Prop :=
  ∃ c : ℝ, 0 < c ∧ m₁ = c • m₀

/-- The projective distance
`d_pr([𝔪_0],[𝔪_1]) = ½ log (λ_max(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}) / λ_min(𝔪_0^{-1/2}𝔪_1𝔪_0^{-1/2}))`
(`e.scale.selection.projective.distance`). -/
def projectiveDistance (m₀ m₁ : Mat d) : ℝ :=
  1 / 2 * Real.log (specBound (normalizedMat m₀ m₁) / specMin (normalizedMat m₀ m₁))

end

end Homogenization.HighContrast
