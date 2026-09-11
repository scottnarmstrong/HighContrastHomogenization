/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CellMajorantAt

/-!
# Splitting a centered cell majorant at the checkpoint

The centered filling rows up to the target scale are partitioned into the rows
at or below the checkpoint and those strictly above it.  This is the exact
matrix identity consumed by the finite-family maximum estimate.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The centered majorant equation split into inherited, fresh, and
below-start blocks. -/
theorem cell_majorant_centered_split {P : Measure (CoeffSpace d)} {q : Mat d}
    {jStar b j : ℤ} (hjb : jStar ≤ b)
    {Z : ℤ → Finset (Fin d → ℤ)} {c : ℤ → ℝ}
    {G : CoeffSpace d → BlockMat d} {KG E : BlockMat d}
    {src : CoeffSpace d → ℝ}
    (hcentered : ∀ᵐ x ∂P, toFullBlockMat (blockSub (G x) KG) =
      (∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r, c r •
        toFullBlockMat (blockSub
          (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r))) +
        src x • toFullBlockMat E) :
    ∀ᵐ x ∂P, toFullBlockMat (blockSub (G x) KG) =
      toFullBlockMat (ofFullBlockMat
        (∑ r ∈ Finset.Icc jStar (min b j), ∑ w ∈ Z r, c r •
          toFullBlockMat (blockSub
            (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r)))) +
      toFullBlockMat (ofFullBlockMat
        (∑ r ∈ Finset.Icc (b + 1) j, ∑ w ∈ Z r, c r •
          toFullBlockMat (blockSub
            (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r)))) +
      toFullBlockMat (blockScale (src x) E) := by
  have hunion : Finset.Icc jStar (min b j) ∪ Finset.Icc (b + 1) j =
      Finset.Icc jStar j := by
    ext r
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc jStar (min b j)) (Finset.Icc (b + 1) j) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    simp only [Finset.mem_Icc] at hr1 hr2
    omega
  filter_upwards [hcentered] with x hx
  rw [hx, toFullBlockMat_ofFullBlockMat, toFullBlockMat_ofFullBlockMat,
    toFullBlockMat_blockScale, ← Finset.sum_union hdisj, hunion]

end

end Transport
end HighContrast
end Homogenization
