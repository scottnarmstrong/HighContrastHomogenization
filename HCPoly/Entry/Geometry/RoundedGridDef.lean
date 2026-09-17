import Homogenization.Ambient.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# The rounded grid `𝒬(𝔪)` — definition only

Near `e.rounded.grid.bounds`.  Fix `j_* ∈ ℕ`.  For every matrix `𝔪`,

  `(𝒬(𝔪))_{ab} := 3^{-j_*} ⌈ 3^{j_*} |𝔪⁻¹|^{1/2} (𝔪^{1/2})_{ab} ⌉`.

Here `|·|` is the Euclidean operator norm (Mathlib's `‖·‖` under `Matrix.Norms.L2Operator`)
and `𝔪^{1/2}` is `CFC.sqrt 𝔪`.  `j_*` is a parameter of the definition (the entries depend
on it); the standing constraint `3^{j_*} ≥ 2d` is a hypothesis on the theorems that use it.

This module is a definition-only leaf: it holds `explicitRoundedGrid` and nothing else.  Every
theorem about `explicitRoundedGrid`, including `e.rounded.grid.bounds`, lives in
`HCPoly.Entry.Geometry.RoundedGrid`, which imports this module.
-/

namespace Homogenization.HighContrast.Geometry

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The rounded grid `𝒬(𝔪)`, entrywise as printed:
`(𝒬(𝔪))_{ab} = 3^{-j_*} ⌈ 3^{j_*} |𝔪⁻¹|^{1/2} (𝔪^{1/2})_{ab} ⌉`.

This is not the `roundedGrid` of `Homogenization.HighContrast`
(`HCPoly/Setup/Geometry.lean`), which takes the scale as an integer and writes the same
entries through `specBound` (the scalar Loewner bound) and `matSqrt` (the chosen
positive-semidefinite square root).  Here the scale is the natural number `j_*` and the
entries are written out with the Euclidean operator norm and `CFC.sqrt`, so the two agree
on positive definite arguments at integer scales but not by unfolding. -/
noncomputable def explicitRoundedGrid (jStar : ℕ) (m : Mat d) : Mat d :=
  Matrix.of fun a b =>
    (3 : ℝ) ^ (-(jStar : ℤ)) * (⌈(3 : ℝ) ^ jStar * Real.sqrt ‖m⁻¹‖ * CFC.sqrt m a b⌉ : ℤ)

end Homogenization.HighContrast.Geometry
