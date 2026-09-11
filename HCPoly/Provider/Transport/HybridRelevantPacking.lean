/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridTargetLayer

/-!
# Packed cells relevant to the hybrid boundary

Only packed cells reached from the uncovered strip by one cell of the other
grid contribute to the packed-boundary tube.  They all lie in one inner layer
of the outer target.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Packed scale-`n` cells that meet a scale-`c` cell containing a point of the
uncovered strip occupy an inner boundary layer of the outer target. -/
theorem volume_relevant_hybridPacking_le [NeZero d] {q q' : Mat d}
    (hq : q.PosDef) (hq' : q'.PosDef) {n l c : ℤ} (y : Vec d)
    {I : Finset (Fin d → ℤ)}
    (hIpack : ∀ w ∈ I, w ∈ hybridPackingIndex q' n
      (adaptedCellTranslate q (n + l) y))
    (hI : ∀ w ∈ I, ∃ x : Vec d, ∃ v : Fin d → ℤ,
      x ∈ hybridStrip q' n (adaptedCellTranslate q (n + l) y) ∧
        x ∉ matVecMul q' '' ⋃ (i : Fin d) (k : ℤ),
          {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ n} ∧
        x ∈ adaptedCellAt q c v ∧
        adaptedCellAt q c v ⊆ adaptedCellTranslate q (n + l) y ∧
        (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty) :
    volume (⋃ w ∈ (I : Set (Fin d → ℤ)), adaptedCellAt q' n w) ≤
      ENNReal.ofReal
          (2 * (d : ℝ) *
            (Real.sqrt d *
              (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n + ‖q⁻¹ * q‖ * (3 : ℝ) ^ c)) *
            (3 : ℝ) ^ (-(n + l))) *
        volume (adaptedCellTranslate q (n + l) y) := by
  let W : Set (Vec d) := adaptedCellTranslate q (n + l) y
  set t : ℝ := Real.sqrt d *
    (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n + ‖q⁻¹ * q‖ * (3 : ℝ) ^ c) with htdef
  have ht : 0 ≤ t := by rw [htdef]; positivity
  have hsub : (⋃ w ∈ (I : Set (Fin d → ℤ)), adaptedCellAt q' n w) ⊆ W := by
    intro s hs
    obtain ⟨w, hwI, hsw⟩ := Set.mem_iUnion₂.mp hs
    exact (hIpack w (Finset.mem_coe.mp hwI)).2.1 hsw
  have hclose : ∀ s ∈ (⋃ w ∈ (I : Set (Fin d → ℤ)), adaptedCellAt q' n w),
      ∃ z : Vec d, z ∉ W ∧ ∀ i, |matVecMul q⁻¹ (s - z) i| ≤ t := by
    intro s hs
    obtain ⟨w, hwI, hsw⟩ := Set.mem_iUnion₂.mp hs
    have hwIf : w ∈ I := Finset.mem_coe.mp hwI
    obtain ⟨x, v, hxSigma, hxface, hxv, hvW, hvw⟩ := hI w hwIf
    obtain ⟨u, hxu⟩ := exists_mem_adaptedCellAt hq' n hxface
    have huout : ¬ adaptedCellAt q' n u ⊆ W := by
      intro huW
      have hupid : u ∈ hybridPackingIndex q' n W := by
        change n ≤ n ∧ adaptedCellAt q' n u ⊆ W ∧
          (n = n ∨ ¬ adaptedCellAt q' (n + 1) (gridParent u) ⊆ W)
        exact ⟨le_rfl, huW, Or.inl rfl⟩
      apply hxSigma.2
      exact Set.mem_iUnion₂.mpr ⟨u, hupid, hxu⟩
    obtain ⟨z, hzu, hzW⟩ := Set.not_subset.mp huout
    refine ⟨z, hzW, fun i => ?_⟩
    obtain ⟨r, hrv, hrw⟩ := hvw
    have hsr := abs_matVecMul_inv_sub_le_of_mem_adaptedCellAt
      (p := q) hsw hrw i
    have hrx := abs_matVecMul_inv_sub_le_of_mem_adaptedCellAt
      (p := q) hrv hxv i
    have hxz := abs_matVecMul_inv_sub_le_of_mem_adaptedCellAt
      (p := q) hxu hzu i
    have hcoord : matVecMul q⁻¹ (s - z) i =
        matVecMul q⁻¹ (s - r) i + matVecMul q⁻¹ (r - x) i +
          matVecMul q⁻¹ (x - z) i := by
      have hvec : s - z = (s - r) + (r - x) + (x - z) := by abel
      rw [hvec, matVecMul_add, matVecMul_add]
      rfl
    rw [hcoord, htdef]
    calc
      |matVecMul q⁻¹ (s - r) i + matVecMul q⁻¹ (r - x) i +
          matVecMul q⁻¹ (x - z) i| ≤
          |matVecMul q⁻¹ (s - r) i| + |matVecMul q⁻¹ (r - x) i| +
            |matVecMul q⁻¹ (x - z) i| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ ‖q⁻¹ * q'‖ * (Real.sqrt d * (3 : ℝ) ^ n) +
          ‖q⁻¹ * q‖ * (Real.sqrt d * (3 : ℝ) ^ c) +
            ‖q⁻¹ * q'‖ * (Real.sqrt d * (3 : ℝ) ^ n) := by
        exact add_le_add (add_le_add hsr hrx) hxz
      _ = Real.sqrt d *
          (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n + ‖q⁻¹ * q‖ * (3 : ℝ) ^ c) := by
        ring
  have h := volume_le_of_close_outside hq ht hsub hclose
  simpa only [htdef] using h

end

end Transport
end HighContrast
end Homogenization
