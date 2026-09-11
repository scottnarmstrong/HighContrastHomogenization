/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.StandardWitness
import HCPoly.Provider.Window.AdaptedRows

/-!
# The stopped multiplier on adapted cells

The simultaneous standard-cell event feeds the maximal filling of every
deterministic rounded adapted cell.  The same stopped multiplier therefore
controls both response orientations throughout the original window.
-/

namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Almost-sure finiteness of the strict successor supplies both adapted-cell
rows simultaneously throughout the original window. -/
theorem ae_adapted_rows_of_successor_ne_top
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {Q K : ℝ} {jStar M : ℤ} (hwindow : IsCoupledWindow d Q K jStar M)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {P : Measure (CoeffSpace d)} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (hfinite : ∀ᵐ a ∂P, successorScale g E (M - jStar) a ≠ ⊤) :
    ∀ᵐ a ∂P, ∀ (n : Mat d), n.PosDef → ∀ (r : ℤ) (y : Vec d),
      adaptedCellTranslate (roundedGrid jStar n) r y ⊆ centeredCube d M →
        BlockMatLoewnerLE
            (coarseBlock (adaptedCellTranslate (roundedGrid jStar n) r y) a)
            (blockScale
              (boundaryConst Cd g n * windowMultiplier g E jStar M a *
                burnDiscount g jStar r) E) ∧
          BlockMatLoewnerLE
            (coarseStarInv (adaptedCellTranslate (roundedGrid jStar n) r y) a)
            (blockScale
              (boundaryConst Cd g n * windowMultiplier g E jStar M a *
                burnDiscount g jStar r) (blockReflect E)) := by
  have hburn : (kZero d : ℤ) ≤ sourceBurn d Q K := by
    rw [sourceBurn]
    exact le_max_left _ _
  have hj : (kZero d : ℤ) ≤ jStar := hburn.trans hwindow.1
  have hstandard := ae_standard_rows_of_successor_ne_top
    (show 0 < d by omega) hg.1 hdag hfinite
  filter_upwards [hstandard] with a ha
  intro n hn r y hcontained
  have hY : 0 ≤ windowMultiplier g E jStar M a :=
    (one_le_windowMultiplier hg.1 E jStar M a).trans' zero_le_one
  apply adapted_rows_of_standard hd hg hj hCd hn hdag.refBlock_posDef hY r y
  intro k w hcell
  exact (ha k w (hcell.trans hcontained)).1

end

end Window
end HighContrast
end Homogenization
