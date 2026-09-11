/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.StandardToAdapted

/-!
# Adapted response rows inside a coupled window

The adjoint row is the block reflection of the primal row.  A standard-cell
bound indexed by centers in the macroscopic window therefore supplies both
rows on every rounded adapted-cell translate contained in that window.
-/

namespace Homogenization
namespace HighContrast
namespace Window

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-- A simultaneous standard-cell primal bound supplies both orientations of
the response on a rounded adapted-cell translate. -/
theorem adapted_rows_of_standard
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {jStar : ℤ} (hj : (kZero d : ℤ) ≤ jStar)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef) {a : CoeffSpace d} {E : BlockMat d}
    (hE : Book.Ch02.BlockPosDef E) {Y : ℝ} (hY : 0 ≤ Y)
    (r : ℤ) (y : Vec d)
    (hstandard : ∀ (k : ℤ) (w : Fin d → ℤ),
      standardCell d k w ⊆
        adaptedCellTranslate (roundedGrid jStar n) r y →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale (Y * burnDiscount g jStar k) E)) :
    BlockMatLoewnerLE
        (coarseBlock (adaptedCellTranslate (roundedGrid jStar n) r y) a)
        (blockScale (boundaryConst Cd g n * Y * burnDiscount g jStar r) E) ∧
      BlockMatLoewnerLE
        (coarseStarInv (adaptedCellTranslate (roundedGrid jStar n) r y) a)
        (blockScale (boundaryConst Cd g n * Y * burnDiscount g jStar r)
          (blockReflect E)) := by
  have hprimal := adapted_primal_of_standard hd hg hj hCd hn hE hY r y hstandard
  refine ⟨hprimal, ?_⟩
  simpa only [Transport.coarseStarInv_eq_blockReflect, Transport.blockScale_blockReflect] using
    Transport.blockMatLoewnerLE_blockReflect hprimal

end

end Window
end HighContrast
end Homogenization
