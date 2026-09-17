import HCPoly.Entry.Setup.BlockCalculus

/-!
# The mean penalty `Ψ_Q(P)`

Near `e.scale.selection.fluctuation.history`:

> For `P ≥ I_{2d}`, set `Ψ_Q(P) := (1 + tr(P - I_{2d}))^Q - 1`.

Transcribed literally, with `I_{2d}` CoarseGraining's `Book.Ch02.blockIdentity d` and `tr`
the trace of the `2d`-by-`2d` matrix.  `Q` is the fixed even moment of
`e.scale.selection.Q.choice`; it is a parameter here rather than `bigQ d γ`, because the
display fixes `Q` once and for all and every consumer passes the same value.

The printed hypothesis `P ≥ I_{2d}` is not part of the definition: the formula is a total
function of `P`, and on blocks that are not above the identity it takes the value the
formula gives (which may be negative).  The hypothesis stays with the consumer.  Under the
real-valued reading of the histories and the profile such a value is carried
through unchanged: `HCPoly/Entry/Setup/Histories.lean` sums `Ψ_Q` in `ℝ`, so nothing is truncated,
and the sign of `Ψ_Q` is the consumer's business rather than a junk branch of an insertion
into `ℝ≥0∞`.

The print subtracts the matrix inside the trace, and the moment is the natural number `Q`.
-/

open Homogenization.HighContrast (blockSub blockTrace)
namespace Homogenization.HighContrast

noncomputable section

variable {d : ℕ}

/-- The mean penalty `Ψ_Q(P) = (1 + tr(P - I_{2d}))^Q - 1` near `e.scale.selection.fluctuation.history`. -/
def meanPenalty (Q : ℕ) (P : BlockMat d) : ℝ :=
  (1 + blockTrace (blockSub P (Book.Ch02.blockIdentity d))) ^ Q - 1

end

end Homogenization.HighContrast
