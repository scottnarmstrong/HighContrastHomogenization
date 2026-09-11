/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridTubeAbsorption

/-!
# Rows of the reverse hybrid filling

After the scale-`n` packed cells are removed, the maximal filling of the
uncovered strip has the same outer-target normalization as the packed row.
The escaping parent at scale `a + 1` supplies the extra geometric factor.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Every row in the maximal filling of the hybrid strip is finite. -/
theorem finite_hybridFillingIndex {q q' : Mat d} (hq : q.PosDef)
    {n l a : ℤ} (y : Vec d) :
    (fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) a).Finite := by
  apply finite_fillingIndex hq
  obtain ⟨R, hR, hbound⟩ := isBoundedDomain_adaptedCellTranslate hq (n + l) y
  exact ⟨R, hR, fun x hx => hbound x (hybridStrip_subset hx)⟩

/-- A selected row in the uncovered strip obeys the packed-boundary tube
estimate at the scale of its escaping parents. -/
theorem volume_hybridFilling_row_le {q q' : Mat d} (hd : 2 ≤ d)
    (hq : q.PosDef) (hq' : q'.PosDef) {n l a : ℤ} (han : a < n)
    (y : Vec d) :
    volume (⋃ w ∈ fillingIndex q n
        (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) a,
          adaptedCellAt q a w) ≤
      ENNReal.ofReal
          ((2 * (d : ℝ) * Real.sqrt d +
              (2 * (d : ℝ) * Real.sqrt d) *
                (2 * (d : ℝ) * Real.sqrt d) * 2 *
                  (1 + 6 * Real.sqrt d) ^ (d - 1)) *
            gridRatio q q' * (3 : ℝ) ^ (a + 1 - (n + l))) *
        volume (adaptedCellTranslate q (n + l) y) := by
  apply volume_le_of_escaping_hybridStrip hd hq hq' (by omega) y
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact adaptedCellAt_subset_of_mem_fillingIndex hw hxw
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨gridParent w, adaptedCellAt_subset_parent q a w hxw,
      hw.2.2.resolve_left (by omega)⟩

/-- The relative-volume form of the reverse hybrid row. -/
theorem sum_relative_volume_hybridFilling_row_le {q q' : Mat d}
    (hd : 2 ≤ d) (hq : q.PosDef) (hq' : q'.PosDef)
    {n l a : ℤ} (han : a < n) (y : Vec d)
    {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) a) :
    ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
        (volume (adaptedCellTranslate q (n + l) y)).toReal ≤
      (2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d) *
            (2 * (d : ℝ) * Real.sqrt d) * 2 *
              (1 + 6 * Real.sqrt d) ^ (d - 1)) *
        gridRatio q q' * (3 : ℝ) ^ (a + 1 - (n + l)) := by
  have hWtop := volume_adaptedCellTranslate_ne_top q (n + l) y
  have hWpos : (0 : ℝ) <
      (volume (adaptedCellTranslate q (n + l) y)).toReal :=
    ENNReal.toReal_pos (volume_adaptedCellTranslate_ne_zero hq (n + l) y) hWtop
  have hmemZ : ∀ w ∈ Z, w ∈ fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) a := by
    intro w hw
    rw [← hZ]
    exact Finset.mem_coe.mpr hw
  have hcelltop : ∀ w ∈ Z, volume (adaptedCellAt q a w) ≠ ⊤ := by
    intro w hw
    refine ne_top_of_le_ne_top hWtop (measure_mono ?_)
    exact (adaptedCellAt_subset_of_mem_fillingIndex (hmemZ w hw)).trans
      hybridStrip_subset
  have hdisj : (↑Z : Set (Fin d → ℤ)).PairwiseDisjoint
      fun w => adaptedCellAt q a w := by
    intro w hw v hv hwv
    exact disjoint_of_mem_fillingIndex hq (hmemZ w (Finset.mem_coe.mp hw))
      (hmemZ v (Finset.mem_coe.mp hv)) (by simpa using hwv)
  have hmeas : ∀ w ∈ Z, MeasurableSet (adaptedCellAt q a w) := fun w _ =>
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq a w).isOpen.measurableSet
  have hsum : ∑ w ∈ Z, volume (adaptedCellAt q a w) =
      volume (⋃ w ∈ fillingIndex q n
        (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) a,
          adaptedCellAt q a w) := by
    rw [← measure_biUnion_finset hdisj hmeas, ← Finset.set_biUnion_coe, hZ]
  have hC0 : 0 ≤
      (2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d) *
            (2 * (d : ℝ) * Real.sqrt d) * 2 *
              (1 + 6 * Real.sqrt d) ^ (d - 1)) *
        gridRatio q q' * (3 : ℝ) ^ (a + 1 - (n + l)) := by
    rw [gridRatio]
    positivity
  rw [← Finset.sum_div, ← ENNReal.toReal_sum hcelltop, hsum,
    div_le_iff₀ hWpos]
  have hle := volume_hybridFilling_row_le (l := l) hd hq hq' han y
  have hmono := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWtop) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at hmono

end

end Transport
end HighContrast
end Homogenization
