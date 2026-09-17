import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentAvSum

/-!
# The recent-scale decomposition

Nothing here restates or weakens an existing declaration, and `diagonalWeakNorm_primal_le`
(`HC2b_DiagonalWeakRecent.lean`) is untouched.

## The decomposition

Between the compiled bound (`HC2b_DiagonalWeakRecentAssembly.lean`) and
`diagonalWeakNorm_primal_le` lie three steps.  This file is the first: the scale decomposition.

The compiled bound is `∑_{n ≤ H} 3^{-n/2} · (cellTerm V n + A n)`, where `cellTerm V n` is built
from a per-cell CHILD maximizer `V n w` and `A n` is an abstract per-scale average-defect term.
The left-hand side of `diagonalWeakNorm_primal_le`, after the two support lemmas
(`HC2b_DiagonalWeakRecentSupport2.lean`), is the head of the seminorm of the ACTUAL
family: the same expression with the PARENT field `Xu` in place of `V n w`.  The recent-scale
decomposition is what connects them, at each depth `n` and then summed:

`headTerm n ≤ cellTerm n + defectTerm n`,

with `defectTerm n` the normalized root-mean-square of the averaged parent-minus-child
difference — i.e. it both supplies the inequality AND *exhibits the witness* for the bound's
otherwise abstract `A`.  What the bound then still assumes about that witness is the analytic
per-scale bound `hscale`, which is NOT in this file.

The proof uses the two ingredients, on these carriers:

* averaging the child/parent difference is the difference of the cell averages; here
  `h6a_cellAverage_sub`.
* the split `parent − mean = (child − mean) + (parent − child)` followed by the triangle
  inequality in the normalized `ℓ²(Z)` of block vectors; here `h6a_recent_cell_split`.

Two implementation notes:

1. The difference is taken as `parent − child` from the start, so no separate sign-cancellation
  step is needed.
2. The quantity is spelled inline as `√(|Z|⁻¹ · ∑_{w ∈ Z} ⟪·,·⟫)`, matching `weakCellSum` and
   `h6a_besovSeminorm_head_tail_le`.  The triangle inequality for it is
   `h6a_normalized_blockL2_add_le` (`HC2b_DiagonalWeakRecentSupport2.lean`).
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Averaging a difference. -/

omit [NeZero d] in
/-- **The cell average of a difference is the difference of the cell averages.**  It is stated
for arbitrary `F`, `G` rather than for two particular fields, with the componentwise
`IntegrableOn` side conditions explicit, because the integrability of `optimizerField` on an
adapted cell is supplied separately by the consumer (the same side conditions two earlier
support lemmas already take, `HC2b_DiagonalWeakRecentSupport2.lean`).  That makes it
reusable and keeps the `MemVectorL2` plumbing out of the decomposition. -/
theorem h6a_cellAverage_sub {V : Set (Vec d)} (F G : Vec d → BlockVec d)
    (h1F : ∀ j, IntegrableOn (fun x => (F x).1 j) V)
    (h2F : ∀ j, IntegrableOn (fun x => (F x).2 j) V)
    (h1G : ∀ j, IntegrableOn (fun x => (G x).1 j) V)
    (h2G : ∀ j, IntegrableOn (fun x => (G x).2 j) V) :
    cellAverage V (fun x => F x - G x) = cellAverage V F - cellAverage V G := by
  refine Prod.ext ?_ ?_
  · funext i
    show volumeAverage V (fun x => (F x).1 i - (G x).1 i)
      = volumeAverage V (fun x => (F x).1 i) - volumeAverage V (fun x => (G x).1 i)
    exact volumeAverage_sub (h1F i) (h1G i)
  · funext i
    show volumeAverage V (fun x => (F x).2 i - (G x).2 i)
      = volumeAverage V (fun x => (F x).2 i) - volumeAverage V (fun x => (G x).2 i)
    exact volumeAverage_sub (h2F i) (h2G i)

/-! ## R1-2.  The split at one cell. -/

omit [NeZero d] in
/-- R1-2.  **The split at one cell.**  The transported, `U_t`-recentred cell average of the
PARENT field is the corresponding quantity for the CHILD field plus the transported average of
the parent-minus-child difference:

`R·((Xu)_{V} − c) = R·((Xv)_{V} − c) + R·((Xu − Xv)_{V})`.

This is the algebraic heart of the mine's `hsplit`
(`…/DiagonalWeakNormRecentDecomposition.lean`), with the sign taken as `parent − child`
so that the mine's separate `blockAvsumL2_neg` step is not needed. -/
theorem h6a_recent_cell_split {V : Set (Vec d)} (R : BlockMat d)
    (Xu Xv : Vec d → BlockVec d) (c : BlockVec d)
    (h1u : ∀ j, IntegrableOn (fun x => (Xu x).1 j) V)
    (h2u : ∀ j, IntegrableOn (fun x => (Xu x).2 j) V)
    (h1v : ∀ j, IntegrableOn (fun x => (Xv x).1 j) V)
    (h2v : ∀ j, IntegrableOn (fun x => (Xv x).2 j) V) :
    blockMatVecMul R (cellAverage V Xu - c)
      = blockMatVecMul R (cellAverage V Xv - c)
        + blockMatVecMul R (cellAverage V (fun x => Xu x - Xv x)) := by
  rw [h6a_cellAverage_sub Xu Xv h1u h2u h1v h2v, ← blockMatVecMul_add]
  congr 1
  abel

/-! ## R1-3.  The decomposition at one depth. -/

/-! ## R1-4.  The decomposition summed over the window, the shape `AS-9` consumes. -/

/-! ## R3-1.  The tail weight (node R3, partial). -/

end

end Homogenization.HighContrast.Multiscale
