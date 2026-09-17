import HCPoly.Setup.Geometry
import HCPoly.Setup.Moments

/-!
# The aligned cells of an adapted grid

Near `e.rounded.grid.bounds` the paper fixes the rounded geometry `q = 𝒬(𝔪)` and the
adapted cell `⋄_j^q = q □_j`, and then indexes everything by the aligned centers
`z ∈ 3^j q ℤ^d`: the fluctuation `V^q_{j,k}(z)` is read on `z + ⋄_j^q` (near `e.scale.selection.normalized.mean.fluctuation`), the
fluctuation history maximizes over `z ∈ 3^j q ℤ^d ∩ ⋄_m^q` (near `e.scale.selection.fluctuation.history`), and the Whitney
families of `l.two.grid.whitney` are families of cells `z + ⋄_r^q` with `z ∈ 3^r q ℤ^d`.

`HCPoly/Entry/Geometry/AdaptedCellDef.lean` has `adaptedCell q j` and the translate
`adaptedCellTranslate q j y` by an arbitrary vector.  This file adds the aligned part: the
center `3^j q w` of the cell at the integer index `w`, the lattice `3^j q ℤ^d` of such
centers, and the cell at an index.  Nothing here depends on `q` being a rounded grid; the
printed hypothesis `q = 𝒬(𝔪)` stays with the consumer, exactly as it does in
`HCPoly/Entry/Geometry/AdaptedCell.lean`.

The import is the definition-only leaf `HCPoly/Entry/Geometry/AdaptedCellDef.lean`, not the proof module
`HCPoly/Entry/Geometry/AdaptedCell.lean` that imports it; the three declarations below and their
elaborated values are unchanged.

`adaptedCellCenter` is the center `3^j q w` of the cell at the integer index `w`, and
`adaptedCellAtCenter` is the translate of that cell, defined through `adaptedCellTranslate`.
`adaptedLatticeAtScale` is the scaled lattice `3^j q ℤ^d`, not `q ℤ^d`: the generation `j` is a
parameter here, and every printed use is of the scaled lattice.
-/

open Homogenization.HighContrast (adaptedCellCenter)
open Homogenization.HighContrast (adaptedCellTranslate)
namespace Homogenization.HighContrast


noncomputable section

variable {d : ℕ}

/-- The aligned lattice `3^j q ℤ^d` of cell centres at scale `j`.

This is not the `adaptedLattice` of the published `HCPoly` library
(`HCPoly/Setup/Geometry.lean`), which takes no scale argument and is the unscaled lattice
`q ℤ^d`.  `adaptedLatticeAtScale q j` is the image of that lattice under `x ↦ 3^j x`, so the
two agree only at `j = 0`. -/
def adaptedLatticeAtScale (q : Mat d) (j : ℤ) : Set (Vec d) :=
  Set.range (adaptedCellCenter q j)

/-- The aligned adapted cell `z + ⋄_j^q` at the integer index `w`, i.e. at the centre
`z = 3^j q w ∈ 3^j q ℤ^d`, written as the translate of `⋄_j^q` by that centre.

The `adaptedCellAt` of the published `HCPoly` library (`HCPoly/Setup/Geometry.lean`) is the
same set of points, written directly as the image of `adaptedCell q j` under `x ↦ 3^j q w + x`.
The two are equal by unfolding `adaptedCellTranslate` and `adaptedCellCenter`, but neither is
the other's normal form, so a `simp` or `rw` lemma about one does not fire on the other. -/
def adaptedCellAtCenter (q : Mat d) (j : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  adaptedCellTranslate q j (adaptedCellCenter q j w)

end

end Homogenization.HighContrast
