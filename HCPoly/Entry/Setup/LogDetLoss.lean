import HCPoly.Entry.Setup.NormalizedFluctuation
import HCPoly.Setup.CoefficientSpace

/-!
# The log-determinant loss `Δ^q_{j,k}` and the synchronized loss `Δ̂^q_h(m)`

Near `e.scale.selection.logdet.loss` (`e.scale.selection.logdet.loss` and
`e.scale.selection.synchronized.loss`):

> For `j ≤ k`, set `Δ^q_{j,k} := log det 𝐀hom_{j,q} − log det 𝐀hom_{k,q} ≥ 0`.  For an
> integer `h ≥ 1`, set `Δ̂^q_h(m) := ∑_{a=m+1}^{m+h} Δ^q_{a−h,a}`.

Both are transcribed literally, with `log det` the `blockLogDet` of
`HCPoly/Entry/Setup/BlockCalculus.lean` and the sum a `Finset.Icc` over the printed range.

Three printed side conditions are not part of the definitions: `j ≤ k`, `h ≥ 1`, and the
assertion `Δ^q_{j,k} ≥ 0` — the last is a statement about the value (the annealed blocks
decrease in the generation), not a part of the formula, and is proved.  On
`h ≤ 0` the index set `Icc (m+1) (m+h)` is empty and the synchronized loss is `0`.

Reference (specification only): `b478920`
`HCPoly/Setup/Moments.lean` (`detIncrement`) (`synchCharge`),
`HCPoly/Setup/Moments.lean` (`blockLogDet`).  Adopted: both shapes, including the
`Finset.Icc (m+1) (m+h)` range of the synchronized sum.  **Not** adopted:
`HCPoly/Setup/TransportObjects.lean` (`detLoss`), which is
`log Ξ^q_u − log Ξ^q_v` for the determinant root `Ξ(E) = det(E)^{1/d}`; that is a
different quantity from this manuscript's `Δ^q_{j,k}`, which takes the logarithm of the
determinant itself.
-/

open Homogenization.HighContrast (CoeffSpace adaptedMean blockLogDet)
namespace Homogenization.HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The log-determinant loss
`Δ^q_{j,k} = log det 𝐀hom_{j,q} − log det 𝐀hom_{k,q}` (`e.scale.selection.logdet.loss`). -/
def logDetLoss (P : Measure (CoeffSpace d)) (q : Mat d) (j k : ℤ) : ℝ :=
  blockLogDet (adaptedMean P q j) - blockLogDet (adaptedMean P q k)

/-- The synchronized loss `Δ̂^q_h(m) = ∑_{a=m+1}^{m+h} Δ^q_{a−h,a}`
(`e.scale.selection.synchronized.loss`). -/
def synchronizedLogDetLoss (P : Measure (CoeffSpace d)) (q : Mat d) (h m : ℤ) : ℝ :=
  ∑ a ∈ Finset.Icc (m + 1) (m + h), logDetLoss P q (a - h) a

end

end Homogenization.HighContrast
