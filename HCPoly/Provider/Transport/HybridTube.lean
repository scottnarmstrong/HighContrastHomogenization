/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridRelevantPacking

/-!
# The tube around the packed-union boundary

The boundary of the uncovered hybrid strip has two parts.  A cell can escape
through the outer target, or through a packed cell.  The first part is the
ordinary Whitney layer; the second is the sum of the outside collars of the
relevant packed cells.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The raw packed-union tube estimate, retaining the two geometric
coefficients before their absorption into the symmetric grid ratio. -/
theorem volume_le_of_escaping_hybridStrip_raw [NeZero d] {q q' : Mat d}
    (hq : q.PosDef) (hq' : q'.PosDef) {n l c : ℤ} (hcn : c ≤ n)
    (y : Vec d) {A : Set (Vec d)}
    (hA : A ⊆ hybridStrip q' n (adaptedCellTranslate q (n + l) y))
    (hesc : ∀ x ∈ A, ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
      ¬ adaptedCellAt q c v ⊆
        hybridStrip q' n (adaptedCellTranslate q (n + l) y)) :
    volume A ≤
      (ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * ‖q⁻¹ * q‖ *
            (3 : ℝ) ^ (c - (n + l))) +
        ENNReal.ofReal
            (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
              (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                (3 : ℝ) ^ (c - n)) *
          ENNReal.ofReal
            (2 * (d : ℝ) *
              (Real.sqrt d *
                (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n +
                  ‖q⁻¹ * q‖ * (3 : ℝ) ^ c)) *
              (3 : ℝ) ^ (-(n + l)))) *
        volume (adaptedCellTranslate q (n + l) y) := by
  classical
  let W : Set (Vec d) := adaptedCellTranslate q (n + l) y
  let Sigma : Set (Vec d) := hybridStrip q' n W
  let F : Set (Vec d) := matVecMul q' '' ⋃ (i : Fin d) (k : ℤ),
    {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ n}
  have hFnull : volume F = 0 := volume_image_gridFaces q' n
  rw [← measure_diff_null (s := A) hFnull]
  have hWbounded : IsBoundedDomain W :=
    isBoundedDomain_adaptedCellTranslate hq (n + l) y
  let hpackfin := finite_hybridPackingIndex hq' (n := n) hWbounded
  let Zp : Finset (Fin d → ℤ) := hpackfin.toFinset
  have hZp : (Zp : Set (Fin d → ℤ)) = hybridPackingIndex q' n W :=
    hpackfin.coe_toFinset
  let I : Finset (Fin d → ℤ) := Zp.filter fun w =>
    ∃ x ∈ A \ F, ∃ v : Fin d → ℤ,
      x ∈ adaptedCellAt q c v ∧ adaptedCellAt q c v ⊆ W ∧
        (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty
  let O : Set (Vec d) := {x | x ∈ A \ F ∧
    ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
      ¬ adaptedCellAt q c v ⊆ W}
  have hIpack : ∀ w ∈ I, w ∈ hybridPackingIndex q' n W := by
    intro w hw
    exact hZp ▸ (Finset.mem_filter.mp hw).1
  have hI : ∀ w ∈ I, ∃ x : Vec d, ∃ v : Fin d → ℤ,
      x ∈ Sigma ∧ x ∉ F ∧ x ∈ adaptedCellAt q c v ∧
        adaptedCellAt q c v ⊆ W ∧
        (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty := by
    intro w hw
    obtain ⟨_, hx⟩ := Finset.mem_filter.mp hw
    obtain ⟨x, hxAF, v, hxv, hvW, hvw⟩ := hx
    exact ⟨x, v, hA hxAF.1, hxAF.2, hxv, hvW, hvw⟩
  have hcover : A \ F ⊆ O ∪
      ⋃ w ∈ (I : Set (Fin d → ℤ)),
        {x : Vec d | x ∉ adaptedCellAt q' n w ∧
          ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
            (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty} := by
    intro x hx
    obtain ⟨v, hxv, hvSigma⟩ := hesc x hx.1
    by_cases hvW : adaptedCellAt q c v ⊆ W
    · right
      obtain ⟨z, hzv, hzSigma⟩ := Set.not_subset.mp hvSigma
      have hzW : z ∈ W := hvW hzv
      have hzpack : z ∈ ⋃ w ∈ hybridPackingIndex q' n W, adaptedCellAt q' n w := by
        by_contra hz
        exact hzSigma ⟨hzW, hz⟩
      obtain ⟨w, hwpack, hzw⟩ := Set.mem_iUnion₂.mp hzpack
      have hwZp : w ∈ Zp := by
        have hwset : w ∈ (Zp : Set (Fin d → ℤ)) := hZp.symm ▸ hwpack
        exact Finset.mem_coe.mp hwset
      have hvw : (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty :=
        ⟨z, hzv, hzw⟩
      have hwI : w ∈ I := Finset.mem_filter.mpr
        ⟨hwZp, x, hx, v, hxv, hvW, hvw⟩
      refine Set.mem_iUnion₂.mpr ⟨w, Finset.mem_coe.mpr hwI, ?_⟩
      refine ⟨?_, v, hxv, hvw⟩
      intro hxw
      exact (hA hx.1).2 (Set.mem_iUnion₂.mpr ⟨w, hwpack, hxw⟩)
    · left
      exact ⟨hx, v, hxv, hvW⟩
  have hOuter : volume O ≤
      ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * ‖q⁻¹ * q‖ *
            (3 : ℝ) ^ (c - (n + l))) * volume W := by
    exact volume_le_of_escaping_ancestor hq
      (fun x hx => (hybridStrip_subset (hA hx.1.1)))
      (fun x hx => hx.2)
  have hRelevant := volume_relevant_hybridPacking_le hq hq' y hIpack hI
  have hdisj : (I : Set (Fin d → ℤ)).PairwiseDisjoint
      fun w => adaptedCellAt q' n w := by
    intro w _ v _ hwv
    exact Recurrence.disjoint_adaptedCellAt hq' n (by simpa using hwv)
  have hmeas : ∀ w ∈ I, MeasurableSet (adaptedCellAt q' n w) := fun w _ =>
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq' n w).isOpen.measurableSet
  have hInternal : volume (⋃ w ∈ (I : Set (Fin d → ℤ)),
      {x : Vec d | x ∉ adaptedCellAt q' n w ∧
        ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
          (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty}) ≤
      ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
            (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
              (3 : ℝ) ^ (c - n)) *
        (ENNReal.ofReal
            (2 * (d : ℝ) *
              (Real.sqrt d *
                (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n +
                  ‖q⁻¹ * q‖ * (3 : ℝ) ^ c)) *
              (3 : ℝ) ^ (-(n + l))) * volume W) := by
    calc
      volume (⋃ w ∈ (I : Set (Fin d → ℤ)),
          {x : Vec d | x ∉ adaptedCellAt q' n w ∧
            ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
              (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty})
          ≤ ∑ w ∈ I, volume {x : Vec d | x ∉ adaptedCellAt q' n w ∧
              ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
                (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty} :=
        measure_biUnion_finset_le I _
      _ ≤ ∑ w ∈ I, ENNReal.ofReal
            (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
              (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                (3 : ℝ) ^ (c - n)) * volume (adaptedCellAt q' n w) := by
        exact Finset.sum_le_sum fun w _ => volume_cellNeighbor_outside_le hq' hcn w
      _ = ENNReal.ofReal
            (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
              (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                (3 : ℝ) ^ (c - n)) *
          volume (⋃ w ∈ (I : Set (Fin d → ℤ)), adaptedCellAt q' n w) := by
        rw [← Finset.mul_sum, ← measure_biUnion_finset hdisj hmeas,
          ← Finset.set_biUnion_coe]
      _ ≤ _ := mul_le_mul' le_rfl hRelevant
  calc
    volume (A \ F) ≤ volume (O ∪ ⋃ w ∈ (I : Set (Fin d → ℤ)),
        {x : Vec d | x ∉ adaptedCellAt q' n w ∧
          ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
            (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty}) := measure_mono hcover
    _ ≤ volume O + volume (⋃ w ∈ (I : Set (Fin d → ℤ)),
        {x : Vec d | x ∉ adaptedCellAt q' n w ∧
          ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
            (adaptedCellAt q c v ∩ adaptedCellAt q' n w).Nonempty}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * ‖q⁻¹ * q‖ *
            (3 : ℝ) ^ (c - (n + l))) * volume W +
        ENNReal.ofReal
            (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
              (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                (3 : ℝ) ^ (c - n)) *
          (ENNReal.ofReal
              (2 * (d : ℝ) *
                (Real.sqrt d *
                  (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n +
                    ‖q⁻¹ * q‖ * (3 : ℝ) ^ c)) *
                (3 : ℝ) ^ (-(n + l))) * volume W) := add_le_add hOuter hInternal
    _ = _ := by ring

end

end Transport
end HighContrast
end Homogenization
