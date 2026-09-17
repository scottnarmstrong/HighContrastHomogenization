import HCPoly.Entry.Setup.BlockCalculus

/-!
# The canonical metric `m(F)`

Near `e.scale.selection.canonical.metric`:

> Set `𝐑 := ((0, I_d), (I_d, 0))`.  For a positive `2d`-by-`2d` block `F`, define
> `m(F) := (F^{1/2}(F^{-1/2}𝐑F^{-1}𝐑F^{-1/2})^{1/2}F^{1/2})_{22}^{-1} > 0`.

Transcribed symbol for symbol.  `F^{1/2}` and the inner `(·)^{1/2}` are `matSqrt`, the
canonical positive semidefinite square root of `HCPoly/Setup/BlockAlgebra.lean`; `𝐑` is
`blockSwap`; `(·)_{22}` is the lower-right `d`-by-`d` block, the `.lowerRight` field of the
doubled block; and the outer `(·)^{-1}` is the inverse of that `d`-by-`d` matrix.

The printed hypothesis "positive `F`" and the printed assertion `m(F) > 0` are not part of
the definition: the first stays with the consumer, and the second is a statement about the
value, proved separately.  Off the positive blocks every root and inverse takes its junk
value.

An alternative characterization defines `m(E)` as the positive factor of the factorization
`M(E) = G_{−g(E)}^t diag(m(E), m(E)^{-1}) G_{−g(E)}` of the canonical block `M(E) = E # E^♯`
and reaches the printed formula through a geometric-mean layer.  The printed display is a
closed expression in `F` and is written here as such, which is why the definition below is
called `explicitCanonicalMetric`.
-/

open Homogenization.HighContrast (matSqrt)
namespace Homogenization.HighContrast

noncomputable section

variable {d : ℕ}

/-- The canonical metric
`m(F) = (F^{1/2}(F^{-1/2}𝐑F^{-1}𝐑F^{-1/2})^{1/2}F^{1/2})_{22}^{-1}`
(`e.scale.selection.canonical.metric`), the printed closed expression.

The `canonicalMetric` of the published `HCPoly` library
(`HCPoly/Setup/TransportObjects.lean`) is the same quantity, defined by a characterization rather than by a formula: it
is `canonMetric (toFullBlockMat F)`, the positive factor of the canonical factorization
`M(F) = G_{−g}^t diag(m, m^{-1}) G_{−g}` (`HCPoly/Geometry/Canonical.lean`), selected by the
uniqueness of that factorization.  That the factor is given by the expression below is a
theorem about positive `F`, not a definitional identity, and nothing in this library proves
it, so the two definitions keep different names. -/
def explicitCanonicalMetric (F : BlockMat d) : Mat d :=
  (ofFullBlockMat
        (matSqrt (toFullBlockMat F) *
          matSqrt
            (matSqrt ((toFullBlockMat F)⁻¹) * toFullBlockMat (blockSwap d) *
              (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d) *
              matSqrt ((toFullBlockMat F)⁻¹)) *
          matSqrt (toFullBlockMat F))).lowerRight⁻¹

end

end Homogenization.HighContrast
