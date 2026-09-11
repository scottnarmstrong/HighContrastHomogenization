/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridRows

/-!
# Residual of the reverse hybrid filling

The residual after a finite cutoff is another packed-boundary tube.  Removing
the cutoff-grid faces supplies a containing scale-`J` cell, and the maximal
ancestor rule turns escape from the selected rows into escape from the strip.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The finite-cutoff residual of the hybrid filling has the outer-target tube
rate. -/
theorem volume_hybridFilling_residual_le {q q' : Mat d} (hd : 2 ≤ d)
    (hq : q.PosDef) (hq' : q'.PosDef) {n l J : ℤ} (hJn : J ≤ n)
    (y : Vec d) :
    volume (hybridStrip q' n (adaptedCellTranslate q (n + l) y) \
        ⋃ a ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n
          (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) a,
            adaptedCellAt q a w) ≤
      ENNReal.ofReal
          ((2 * (d : ℝ) * Real.sqrt d +
              (2 * (d : ℝ) * Real.sqrt d) *
                (2 * (d : ℝ) * Real.sqrt d) * 2 *
                  (1 + 6 * Real.sqrt d) ^ (d - 1)) *
            gridRatio q q' * (3 : ℝ) ^ (J - (n + l))) *
        volume (adaptedCellTranslate q (n + l) y) := by
  let F : Set (Vec d) := matVecMul q '' ⋃ (i : Fin d) (k : ℤ),
    {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ J}
  have hFnull : volume F = 0 := volume_image_gridFaces q J
  rw [← measure_diff_null (s := hybridStrip q' n
    (adaptedCellTranslate q (n + l) y) \
      ⋃ a ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n
        (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) a,
          adaptedCellAt q a w) hFnull]
  apply volume_le_of_escaping_hybridStrip hd hq hq' hJn y
  · intro x hx
    exact hx.1.1
  · rintro x ⟨⟨hxSigma, hxnot⟩, hxF⟩
    obtain ⟨w, hxw⟩ := exists_mem_adaptedCellAt hq J hxF
    refine ⟨w, hxw, fun hsub => hxnot ?_⟩
    obtain ⟨b, hbn, hbmem, hbsub⟩ :=
      exists_mem_fillingIndex_of_subset hJn hsub
    exact Set.mem_iUnion₂.mpr ⟨J + (b : ℤ), ⟨by omega, hbn⟩,
      Set.mem_iUnion₂.mpr ⟨gridParent^[b] w, hbmem, hbsub hxw⟩⟩

end

end Transport
end HighContrast
end Homogenization
