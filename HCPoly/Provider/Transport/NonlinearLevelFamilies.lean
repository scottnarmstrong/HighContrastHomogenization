/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.ContinuedLevelData
import HCPoly.Provider.Transport.NonlinearBound

/-!
# The per-level families of the transported nonlinear history

`Transport.nonlinear_bound` is stated over the two regimes of the new grid's target
scales, and its two row hypotheses are discharged — by
`Transport.nonlinear_row_of_filling` on a continued level and by `Transport.cell_gap_early`
on an early one — from data the transport must exhibit at *every* target scale
at once.  `Transport.exists_continued_level_filling` and
`Transport.exists_early_level_upper_mean` produce that data one scale at a time; this
file collects the choices into the `∀ j` families the row hypotheses consume,
and supplies the two remaining pieces of the row's binder.

*The adaptive depth.*  `λ_j` is the printed two-valued depth: one below the
buffer above the checkpoint, the full buffer above it.  It is exhibited as a
function of the target scale, which is all the adaptive bulk kernel and
`Transport.inherited_bulk_depth` require of it.

*The near isometry.*  The datum `SᵗS ≤ (1+η/(1-η))I` is not a property of the
filling: it is the bridge normalization clause of
`p.two.grid.transport` itself, stated there on the bridge Gram.
`Transport.toFullBlockMat_bridgeGram` is what identifies the two.

*The base cell.*  Every target cell is read at its own centre, and an aligned
adapted cell is definitionally the translate of the centred cell by that centre,
so the family's centre is `y_j = 3^jq'0` and the two cell dialects agree with no
rewriting.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The near isometry and the adaptive depth -/

/-- **The bridge normalization clause is the near-isometry hypothesis of the
nonlinear row.**  Clause `b4` of `p.two.grid.transport` is stated on
the bridge Gram; `Transport.toFullBlockMat_bridgeGram` identifies it with `SᵗS`, which
is the datum `e.two.grid.whitney.mean.bound` consumes. -/
theorem bridgeMap_gram_le_of_clause {H F : BlockMat d} {c : ℝ}
    (hclause : BlockMatLoewnerLE (bridgeGram H F)
      (blockScale c (Book.Ch02.blockIdentity d)))
    (hHsym : IsSymmetricBlockMat H) (hHpd : Book.Ch02.BlockPosDef H)
    (hFpd : (toFullBlockMat F).PosDef) :
    (bridgeMap H F)ᵀ * bridgeMap H F ≤ c • (1 : FullBlockMat d) := by
  have hHfull : (toFullBlockMat H).PosDef := posDef_toFullBlockMat hHsym hHpd
  have hgramsym : IsSymmetricBlockMat (bridgeGram H F) :=
    isSymmetricBlockMat_bridgeGram hHfull hFpd
  have hIsym : IsSymmetricBlockMat (Book.Ch02.blockIdentity d) := by
    refine isSymmetricBlockMat_of_posSemidef ?_
    rw [toFullBlockMat_blockIdentity]
    exact Matrix.PosSemidef.one
  have h := le_of_blockMatLoewnerLE hgramsym
    (isSymmetricBlockMat_blockScale _ hIsym) hclause
  rwa [bridgeGram, toFullBlockMat_ofFullBlockMat, toFullBlockMat_blockScale,
    toFullBlockMat_blockIdentity] at h

/-- **The printed adaptive depth.**  `λ_j = 1` below the buffer above the
checkpoint and `λ_j = ℓ₀` above it: the two-valued depth the adaptive bulk
kernel binds, exhibited as a function of the target scale. -/
theorem exists_adaptive_depth (b l0 : ℤ) :
    ∃ lam : ℤ → ℤ, (∀ j, lam j = 1 ∨ lam j = l0) ∧
      (∀ j, j ≤ b + l0 → lam j = 1) ∧ (∀ j, b + l0 < j → lam j = l0) := by
  classical
  refine ⟨fun j => if j ≤ b + l0 then 1 else l0, fun j => ?_,
    fun j hj => if_pos hj, fun j hj => if_neg (by omega)⟩
  by_cases h : j ≤ b + l0
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-! ## The two families -/

end

end Transport
end HighContrast
end Homogenization
