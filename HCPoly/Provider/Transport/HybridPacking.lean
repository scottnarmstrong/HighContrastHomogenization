/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WhitneyRows

/-!
# The packed part of the reverse hybrid filling

This file constructs the packed scale row and its uncovered strip from
`l.two.grid.whitney`.  It proves the packing-fraction estimate in
measure form and the finiteness of the packed row.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The indices of the scale-`n` cells packed inside a target. -/
def hybridPackingIndex (q : Mat d) (n : ℤ) (W : Set (Vec d)) : Set (Fin d → ℤ) :=
  fillingIndex q n W n

/-- The part of the target left uncovered by the packed scale row. -/
def hybridStrip (q : Mat d) (n : ℤ) (W : Set (Vec d)) : Set (Vec d) :=
  W \ ⋃ w ∈ hybridPackingIndex q n W, adaptedCellAt q n w

/-- The packed scale row is finite in a bounded target. -/
theorem finite_hybridPackingIndex {q : Mat d} (hq : q.PosDef) {n : ℤ}
    {W : Set (Vec d)} (hW : IsBoundedDomain W) : (hybridPackingIndex q n W).Finite := by
  rw [hybridPackingIndex]
  exact finite_fillingIndex hq hW n n

/-- The uncovered strip is contained in its target. -/
theorem hybridStrip_subset {q : Mat d} {n : ℤ} {W : Set (Vec d)} :
    hybridStrip q n W ⊆ W :=
  Set.diff_subset

/-- The uncovered strip of the scale-`n` packing lies in a target boundary
layer of width controlled by the packed grid. -/
theorem volume_hybridStrip_le {q q' : Mat d} (hq : q.PosDef) (hq' : q'.PosDef)
    (n l : ℤ) (y : Vec d) :
    volume (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) ≤
      ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ (-(l : ℤ))) *
        volume (adaptedCellTranslate q (n + l) y) := by
  let W : Set (Vec d) := adaptedCellTranslate q (n + l) y
  let F : Set (Vec d) := matVecMul q' '' ⋃ (i : Fin d) (k : ℤ),
    {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ n}
  have hFnull : volume F = 0 := by
    exact volume_image_gridFaces q' n
  rw [← measure_diff_null (s := hybridStrip q' n W) hFnull]
  have hraw := volume_le_of_escaping_ancestor (p := q) (q := q') hq
    (j := n + l) (c := n) (y := y) (A := hybridStrip q' n W \ F)
    (fun _ hx ↦ hx.1.1) (by
      rintro x ⟨hx, hxF⟩
      obtain ⟨w, hxw⟩ := exists_mem_adaptedCellAt hq' n hxF
      refine ⟨w, hxw, ?_⟩
      intro hwW
      have hwidx : w ∈ hybridPackingIndex q' n W := by
        change n ≤ n ∧ adaptedCellAt q' n w ⊆ W ∧
          (n = n ∨ ¬ adaptedCellAt q' (n + 1) (gridParent w) ⊆ W)
        exact ⟨le_rfl, hwW, Or.inl rfl⟩
      apply hx.2
      apply Set.mem_iUnion.mpr
      exact ⟨w, Set.mem_iUnion.mpr ⟨hwidx, hxw⟩⟩)
  refine hraw.trans_eq ?_
  congr 2
  congr 1
  rw [show n - (n + l) = -l by ring]

/-- The packing-fraction estimate with the symmetric cross-grid factor. -/
theorem volume_hybridStrip_le_gridRatio {q q' : Mat d} (hd : 1 ≤ d)
    (hq : q.PosDef) (hq' : q'.PosDef) (n l : ℤ) (y : Vec d) :
    volume (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) ≤
      ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * gridRatio q q' * (3 : ℝ) ^ (-(l : ℤ))) *
        volume (adaptedCellTranslate q (n + l) y) := by
  refine (volume_hybridStrip_le hq hq' n l y).trans ?_
  gcongr
  exact (norm_inv_mul_le_gridRatio hd q q').2

end

end Transport
end HighContrast
end Homogenization
