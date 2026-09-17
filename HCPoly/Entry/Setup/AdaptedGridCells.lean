import HCPoly.Entry.Setup.AdaptedGrid

/-!
# The adapted-grid Whitney families of the two-grid lemma

`l.two.grid.whitney`, the two constructions:

> (i) Let `W = y + ⋄_j^{q'}`, with `y ∈ 3^j q' ℤ^d`.  Select the maximal adapted cubes of
> the `q`-grid contained in `W` whose generations are at most `j − ℓ`.  Denote their centers
> at generation `r` by `𝒵_r(W)`. …
> (ii) Let `W = y + ⋄_j^q`, with `y ∈ 3^j q ℤ^d`.  First take all the adapted cubes
> `z + ⋄_{j−ℓ}^{q'}`, with `z ∈ 3^{j−ℓ} q' ℤ^d`, contained in `W`.  In the uncovered part,
> select the maximal adapted cubes of the `q`-grid whose generations are at most `j − ℓ`,
> and again denote their centers by `𝒵_r(W)`.

`HCPoly/Entry/Geometry/MaximalCells.lean` has exactly this family for the **standard** cubes
`standardCell d k w`, as `IsCellIn`, `IsMaximalCellIn`, `maximalCellIndices`,
`maximalCellPairs`.  This file is that file's four definitions for the **adapted** cells
`adaptedCellAtCenter q r w` of a grid `q`, together with the covered and uncovered parts that
construction (ii) needs.  The definitions are deliberately the same shape, so that the two
families can be compared declaration by declaration.

What is in the print and *not* here, because it is a statement and not a definition: that
the selected cubes partition `W` up to a null set; the three counts of
`e.two.grid.whitney.counts`; and the two volume identities of
`e.two.grid.whitney.volumes`.  In particular the print's `#𝒵_r(W)` presupposes the family to
be finite, which is part of what the lemma asserts; the family is a `Set` here, and a
statement about its cardinality is written with `Set.ncard` or by exhibiting a `Finset`.

Both constructions take the generation bound `j − ℓ` as a single argument: nothing here
depends on how it is composed, and the printed hypotheses (`W` a cell of the other grid,
`y` aligned, `ℓ ≥ 1`, `K(q,q') ≤ K_0`) stay with the consumer.

-/

open Homogenization.HighContrast (adaptedCellCenter)
namespace Homogenization.HighContrast

noncomputable section

variable {d : ℕ}

/-- `adaptedCellAtCenter q r w` is a member of the family: generation at most `j` and contained in
`W`.  The adapted-grid analogue of `Geometry.IsCellIn`. -/
def IsAdaptedCellIn (W : Set (Vec d)) (q : Mat d) (j r : ℤ) (w : Fin d → ℤ) : Prop :=
  r ≤ j ∧ adaptedCellAtCenter q r w ⊆ W

/-- `adaptedCellAtCenter q r w` is a maximal member of the family of adapted cells of the `q`-grid
contained in `W` with generation at most `j`: it belongs to the family and every member
containing it is equal to it.  The adapted-grid analogue of `Geometry.IsMaximalCellIn`. -/
def IsMaximalAdaptedCellIn (W : Set (Vec d)) (q : Mat d) (j r : ℤ) (w : Fin d → ℤ) : Prop :=
  IsAdaptedCellIn W q j r w ∧
    ∀ r' w', IsAdaptedCellIn W q j r' w' → adaptedCellAtCenter q r w ⊆ adaptedCellAtCenter q r' w' →
      adaptedCellAtCenter q r' w' = adaptedCellAtCenter q r w

/-- The indices `w` of the maximal adapted cells at generation `r`. -/
def maximalAdaptedCellIndices (W : Set (Vec d)) (q : Mat d) (j r : ℤ) : Set (Fin d → ℤ) :=
  {w | IsMaximalAdaptedCellIn W q j r w}

/-- The centers `𝒵_r(W)` of the maximal adapted cells at generation `r`: the points
`3^r q w ∈ 3^r q ℤ^d` at which those cells sit. -/
def maximalAdaptedCellCenters (W : Set (Vec d)) (q : Mat d) (j r : ℤ) : Set (Vec d) :=
  adaptedCellCenter q r '' maximalAdaptedCellIndices W q j r

/-- The part of `W` covered by the adapted cells of the grid `q` at generation `j` that are
contained in `W`: the first family of construction (ii), taken at `q = q'` and
`j = j − ℓ`. -/
def adaptedCoveredPart (W : Set (Vec d)) (q : Mat d) (j : ℤ) : Set (Vec d) :=
  ⋃ w ∈ {w : Fin d → ℤ | adaptedCellAtCenter q j w ⊆ W}, adaptedCellAtCenter q j w

/-- The uncovered part of `W`: what is left of `W` after the adapted cells of the grid `q`
at generation `j` contained in `W` are removed.  Construction (ii) selects its maximal
adapted cells of the other grid. -/
def adaptedUncoveredPart (W : Set (Vec d)) (q : Mat d) (j : ℤ) : Set (Vec d) :=
  W \ adaptedCoveredPart W q j

end

end Homogenization.HighContrast
