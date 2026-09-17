import HCPoly.Setup.BlockAlgebra
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import HCPoly.Setup.Moments

/-!
# The arithmetic the printed displays perform on doubled blocks

The paper writes ordinary matrix operations on `2d`-by-`2d` matrices — a
difference `P - I_{2d}`, a trace, a logarithm of a determinant, the operator norm `|M|`,
the normalization `F^{-1/2} H F^{-1/2}`, and the swap block `𝐑` — while the development
carries a `2d`-by-`2d` matrix as the four-field `BlockMat d`.  This file is the translation
layer those displays need, and nothing else: each definition is the named operation read
through `toFullBlockMat`.

Conventions, stated because a reader comparing this file to the manuscript must not have to
guess (operating rules, the standing honesty rule):

* `|M|` is Mathlib's L2 operator norm, as `HCPoly/Entry/Geometry/QuadraticForm.lean` already fixes it
  for `Mat d`.
* `F^{-1/2}` is `matSqrt (F⁻¹)`, the canonical positive semidefinite square root of the
  inverse fixed in `HCPoly/Setup/BlockAlgebra.lean`; on a block that is not positive definite
  the inverse and the root take their junk values there, so `normalizedBlock` carries no
  positivity hypothesis and the printed hypothesis `F > 0` stays with the consumer.
* `blockLogDet` is `log (det H)`, which is Mathlib's junk `log` of a nonpositive determinant
  off the positive blocks, again by the same convention.

`blockSwap` is CoarseGraining's `Book.Ch02.blockR`, which is already the printed matrix; it is
named here only so that the printed symbol `𝐑` has a Lean name.
-/

namespace Homogenization.HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The operator norm `|H|` of a doubled block: Mathlib's L2 operator norm of the
`2d`-by-`2d` matrix. -/
def blockOpNorm (H : BlockMat d) : ℝ :=
  ‖toFullBlockMat H‖

/-- The swap block `𝐑 = ((0, I_d), (I_d, 0))` near `e.scale.selection.projective.distance`.  This
is CoarseGraining's reflection block `Book.Ch02.blockR`; the printed display is that matrix. -/
def blockSwap (d : ℕ) : BlockMat d :=
  Book.Ch02.blockR d

end

end Homogenization.HighContrast
