import HCPoly.Entry.Setup.AdaptedGrid
import HCPoly.Entry.Setup.BlockCalculus
import HCPoly.Entry.Setup.Response
import HCPoly.Setup.Moments
import HCPoly.Setup.CoefficientSpace

/-!
# The annealed adapted block, the normalized mean `P^q_{j,k}` and the fluctuation `V^q_{j,k}`

Near `e.scale.selection.normalized.mean.fluctuation`:

> For `j ∈ ℤ`, set `⋄_j^q := q □_j` and `𝐀hom_{j,q} := 𝐀hom(⋄_j^q) = E[𝐀(⋄_j^q)]`.  For
> `j ≤ k` and `z ∈ 3^j q ℤ^d`, define the normalized mean and fluctuation by
> `P^q_{j,k} := 𝐀hom_{k,q}^{-1/2} 𝐀hom_{j,q} 𝐀hom_{k,q}^{-1/2}` and
> `V^q_{j,k}(z) := 𝐀hom_{k,q}^{-1/2}(𝐀(z + ⋄_j^q) − 𝐀hom_{j,q})𝐀hom_{k,q}^{-1/2}`.
> … Write `V^q_j := V^q_{j,j}(0)`.

`𝐀(U)` is `coarseBlock U`, `𝐀hom(U)` is `annealedBlock P U` and `⋄_j^q` is `adaptedCell q j`;
the conjugation `F^{-1/2} · F^{-1/2}` is `normalizedBlock` of
`HCPoly/Entry/Setup/BlockCalculus.lean`.

Two things the print carries as hypotheses and these definitions do not, so that a reader
comparing file to manuscript finds no silent divergence (operating rules, the standing
honesty rule):

* `j ≤ k`.  `normalizedMean` and `normalizedFluctuation` are total in both generations.
* `z ∈ 3^j q ℤ^d`.  `normalizedFluctuation` takes an arbitrary translate `z : Vec d`
  through `adaptedCellTranslate`; the aligned centers are `adaptedLatticeAtScale q j` of
  `HCPoly/Entry/Setup/AdaptedGrid.lean`, and a consumer that needs the printed restriction states it.
  The one printed use of a non-aligned argument is `V^q_j = V^q_{j,j}(0)`, and `0` is
  aligned.

`𝐀hom_{k,q}^{-1/2}` is meaningful because the annealed adapted block is positive definite;
that is `blockPosDef_annealedBlock` (`HCPoly/Entry/Setup/Response.lean`), which has
hypotheses.  None of them is imposed here: off the positive definite blocks the inverse and
the square root take the junk values fixed in `HCPoly/Setup/BlockAlgebra.lean`.

The print names the random matrix `V^q_{j,k}(z)` and takes norms of it at the use sites;
`normalizedFluctuation` defines that matrix itself, not its mixed norm.
-/

open Homogenization.HighContrast (CoeffSpace adaptedMean blockSub coarseBlock normalizedBlock)
open Homogenization.HighContrast (adaptedCellTranslate)
namespace Homogenization.HighContrast

open MeasureTheory Geometry

noncomputable section

variable {d : ℕ}

/-- The normalized mean `P^q_{j,k} = 𝐀hom_{k,q}^{-1/2} 𝐀hom_{j,q} 𝐀hom_{k,q}^{-1/2}`
(`e.scale.selection.normalized.mean.fluctuation`). -/
def normalizedMean (P : Measure (CoeffSpace d)) (q : Mat d) (j k : ℤ) : BlockMat d :=
  normalizedBlock (adaptedMean P q j) (adaptedMean P q k)

/-- The normalized fluctuation
`V^q_{j,k}(z) = 𝐀hom_{k,q}^{-1/2}(𝐀(z + ⋄_j^q) − 𝐀hom_{j,q})𝐀hom_{k,q}^{-1/2}`
(`e.scale.selection.normalized.mean.fluctuation`), a random doubled block. -/
def normalizedFluctuation (P : Measure (CoeffSpace d)) (q : Mat d) (j k : ℤ) (z : Vec d)
    (a : CoeffSpace d) : BlockMat d :=
  normalizedBlock
    (blockSub (coarseBlock (adaptedCellTranslate q j z) a) (adaptedMean P q j))
    (adaptedMean P q k)

/-- The diagonal fluctuation `V^q_j = V^q_{j,j}(0)` (near `e.scale.selection.logdet.loss`). -/
def normalizedFluctuationSelf (P : Measure (CoeffSpace d)) (q : Mat d) (j : ℤ)
    (a : CoeffSpace d) : BlockMat d :=
  normalizedFluctuation P q j j 0 a

end

end Homogenization.HighContrast
