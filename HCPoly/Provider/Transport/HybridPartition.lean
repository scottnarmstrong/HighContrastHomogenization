/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridResidual
import HCPoly.Provider.Transport.FillingSubadditivity
import HCPoly.Provider.Transport.WindowCellBounds

/-!
# Finite reverse hybrid sub-partitions

At a finite cutoff, the packed cells and the selected rows in the uncovered
strip form one disjoint family inside the outer target.  The only uncovered
part is the hybrid residual, so finite subadditivity applies with precisely its
outer-target relative volume.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

variable {q q' : Mat d} {n l J : ℤ} {y : Vec d}
  {Zp : Finset (Fin d → ℤ)} {Z : ℤ → Finset (Fin d → ℤ)}

private theorem mem_hybrid_row
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r)
    {r : ℤ} {w : Fin d → ℤ} (hw : w ∈ Z r) :
    w ∈ fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r := by
  rw [← hZ r]
  exact Finset.mem_coe.mpr hw

private theorem mem_hybrid_rows {i : ℤ × (Fin d → ℤ)} :
    i ∈ (Finset.Icc J n).biUnion
        (fun r => (Z r).image (Prod.mk r)) ↔
      i.1 ∈ Finset.Icc J n ∧ i.2 ∈ Z i.1 := by
  classical
  constructor
  · intro hi
    obtain ⟨r, hr, hi⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨hr, hw⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_biUnion.mpr
      ⟨i.1, h1, Finset.mem_image.mpr ⟨i.2, h2, rfl⟩⟩

private theorem sum_hybrid_rows (F : ℤ × (Fin d → ℤ) → ℝ) :
    ∑ i ∈ (Finset.Icc J n).biUnion
        (fun r => (Z r).image (Prod.mk r)), F i =
      ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r, F (r, w) := by
  classical
  rw [Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_image fun _ _ _ _ h => congrArg Prod.snd h
  · intro r _ s _ hrs
    refine Finset.disjoint_left.mpr fun i hi hi' => hrs ?_
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hi'
    exact (congrArg Prod.fst hv).symm

private theorem union_hybrid_family
    (hZp : ↑Zp = hybridPackingIndex q' n
      (adaptedCellTranslate q (n + l) y))
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r) :
    (⋃ i ∈ (↑(Zp.disjSum ((Finset.Icc J n).biUnion
        (fun r => (Z r).image (Prod.mk r))) :
          Set ((Fin d → ℤ) ⊕ (ℤ × (Fin d → ℤ))))),
      Sum.elim (fun w => adaptedCellAt q' n w)
        (fun rw => adaptedCellAt q rw.1 rw.2) i) =
      (⋃ w ∈ hybridPackingIndex q' n
          (adaptedCellTranslate q (n + l) y), adaptedCellAt q' n w) ∪
        ⋃ r ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n
          (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r,
            adaptedCellAt q r w := by
  ext x
  simp only [Set.mem_iUnion, exists_prop, Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨i, hi, hxi⟩
    have hi' : i ∈ Zp.disjSum ((Finset.Icc J n).biUnion
        (fun r => (Z r).image (Prod.mk r))) := Finset.mem_coe.mp hi
    rcases Finset.mem_disjSum.mp hi' with ⟨w, hw, rfl⟩ | ⟨rw, hrw, rfl⟩
    · exact Or.inl ⟨w, hZp ▸ hw, hxi⟩
    · obtain ⟨hr, hw⟩ := mem_hybrid_rows.mp hrw
      exact Or.inr ⟨rw.1, Finset.mem_Icc.mp hr, rw.2,
        mem_hybrid_row hZ hw, hxi⟩
  · rintro (hpack | hrow)
    · obtain ⟨w, hw, hxw⟩ := hpack
      have hwset : w ∈ (↑Zp : Set (Fin d → ℤ)) := hZp.symm ▸ hw
      have hi : Sum.inl w ∈ Zp.disjSum ((Finset.Icc J n).biUnion
          (fun r => (Z r).image (Prod.mk r))) :=
        Finset.inl_mem_disjSum.mpr (Finset.mem_coe.mp hwset)
      exact ⟨Sum.inl w, Finset.mem_coe.mpr hi, hxw⟩
    · obtain ⟨r, hr, w, hw, hxw⟩ := hrow
      have hwZ : w ∈ Z r := by
        rw [← hZ r] at hw
        exact Finset.mem_coe.mp hw
      have hi : Sum.inr (r, w) ∈ Zp.disjSum ((Finset.Icc J n).biUnion
          (fun s => (Z s).image (Prod.mk s))) :=
        Finset.inr_mem_disjSum.mpr
          (mem_hybrid_rows.mpr ⟨Finset.mem_Icc.mpr hr, hwZ⟩)
      exact ⟨Sum.inr (r, w), Finset.mem_coe.mpr hi, hxw⟩

private theorem exists_uniform_blockQuadratic_subpartition [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hU0 : volume U ≠ 0) (a : CoeffSpace d) (X : BlockVec d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {I : Type} (S : Finset I)
      (c : I → Set (Vec d)),
      (∀ i ∈ S, IsOpenBoundedConvexDomain (c i)) →
      (∀ i ∈ S, c i ⊆ U) →
      (↑S : Set I).PairwiseDisjoint c →
      (∀ i ∈ S, volume (c i) ≠ 0) →
      1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock U a) X) ≤
        (∑ i ∈ S, (volume (c i)).toReal / (volume U).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (c i) a) X))) +
          (volume (U \ ⋃ i ∈ (↑S : Set I), c i)).toReal /
            (volume U).toReal * C := by
  obtain ⟨lam, Lam, f, _, _, hfm, hfell, hae⟩ :=
    exists_pointwise_elliptic_representative a.2 hU.isBoundedDomain.isBounded
  refine ⟨|lam⁻¹ * (Lam ^ 2 * vecNormSq X.1 + vecNormSq X.2) -
      vecDot X.1 X.2|, abs_nonneg _, ?_⟩
  intro I S c hc hsub hdisj hcell0
  have hrep : ∀ V : Set (Vec d), coarseBlock V a = coarseBlockMatrix V f :=
    fun V => coarseBlock_eq_of_ae_eq a hae
  simp only [hrep]
  have hbase := blockQuadratic_le_sum_weight_add_residual
    (lam := lam) (Lam := Lam) hU
    (Recurrence.isEllipticFieldOn_of_measurable hfm hfell hU.isOpen.measurableSet)
    hU0 hc hsub hdisj hcell0 X
  refine hbase.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)

/-- Finite subadditivity over the packed row and the selected hybrid rows. -/
theorem exists_blockQuadratic_coarseBlock_le_hybrid_rows [NeZero d]
    (hq : q.PosDef) (hq' : q'.PosDef)
    (hZp : ↑Zp = hybridPackingIndex q' n
      (adaptedCellTranslate q (n + l) y))
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r)
    (a : CoeffSpace d) (X : BlockVec d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ J : ℤ,
      1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCellTranslate q (n + l) y) a) X) ≤
        (∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal /
            (volume (adaptedCellTranslate q (n + l) y)).toReal *
              (1 / 2 * blockVecDot X
                (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
          (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate q (n + l) y)).toReal *
                (1 / 2 * blockVecDot X
                  (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) +
          (volume (hybridStrip q' n (adaptedCellTranslate q (n + l) y) \
            ⋃ r ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n
              (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r,
                adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate q (n + l) y)).toReal * C := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_uniform_blockQuadratic_subpartition
    (isOpenBoundedConvexDomain_adaptedCellTranslate hq (n + l) y)
    (volume_adaptedCellTranslate_ne_zero hq (n + l) y) a X
  refine ⟨C, hC0, fun J => ?_⟩
  let R : Finset (ℤ × (Fin d → ℤ)) := (Finset.Icc J n).biUnion
    (fun r => (Z r).image (Prod.mk r))
  let S : Finset ((Fin d → ℤ) ⊕ (ℤ × (Fin d → ℤ))) := Zp.disjSum R
  let c : (Fin d → ℤ) ⊕ (ℤ × (Fin d → ℤ)) → Set (Vec d) :=
    Sum.elim (fun w => adaptedCellAt q' n w)
      (fun rw => adaptedCellAt q rw.1 rw.2)
  let W : Set (Vec d) := adaptedCellTranslate q (n + l) y
  let Sigma : Set (Vec d) := hybridStrip q' n W
  have hpack : ∀ w ∈ Zp, w ∈ hybridPackingIndex q' n W := by
    intro w hw
    exact hZp ▸ Finset.mem_coe.mpr hw
  have hrow : ∀ i ∈ R, i.2 ∈ fillingIndex q n Sigma i.1 := by
    intro i hi
    change i ∈ (Finset.Icc J n).biUnion
      (fun r => (Z r).image (Prod.mk r)) at hi
    exact mem_hybrid_row hZ (mem_hybrid_rows.mp hi).2
  have hc : ∀ i ∈ S, IsOpenBoundedConvexDomain (c i) := by
    rintro (w | i) hi
    · exact Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq' n w
    · exact Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq i.1 i.2
  have hsub : ∀ i ∈ S, c i ⊆ W := by
    rintro (w | i) hi
    · exact adaptedCellAt_subset_of_mem_fillingIndex (hpack w (by simpa [S] using hi))
    · exact (adaptedCellAt_subset_of_mem_fillingIndex
        (hrow i (by simpa [S] using hi))).trans hybridStrip_subset
  have hdisj : (↑S : Set ((Fin d → ℤ) ⊕ (ℤ × (Fin d → ℤ)))).PairwiseDisjoint c := by
    rintro (w | i) hi (v | k) hk hne
    · exact Recurrence.disjoint_adaptedCellAt hq' n (by simpa using hne)
    · refine Set.disjoint_left.mpr fun x hxw hxk => ?_
      have hxSigma := adaptedCellAt_subset_of_mem_fillingIndex
        (hrow k (by simpa [S] using Finset.mem_coe.mp hk)) hxk
      exact hxSigma.2 (Set.mem_iUnion₂.mpr
        ⟨w, hpack w (by simpa [S] using Finset.mem_coe.mp hi), hxw⟩)
    · refine Set.disjoint_left.mpr fun x hxi hxv => ?_
      have hxSigma := adaptedCellAt_subset_of_mem_fillingIndex
        (hrow i (by simpa [S] using Finset.mem_coe.mp hi)) hxi
      exact hxSigma.2 (Set.mem_iUnion₂.mpr
        ⟨v, hpack v (by simpa [S] using Finset.mem_coe.mp hk), hxv⟩)
    · exact disjoint_of_mem_fillingIndex hq
        (hrow i (by simpa [S] using Finset.mem_coe.mp hi))
        (hrow k (by simpa [S] using Finset.mem_coe.mp hk)) (by simpa using hne)
  have hcell0 : ∀ i ∈ S, volume (c i) ≠ 0 := by
    rintro (w | i) hi
    · exact (Recurrence.volume_adaptedCellAt_pos hq' n w).ne'
    · exact (Recurrence.volume_adaptedCellAt_pos hq i.1 i.2).ne'
  have hmain := hC S c hc hsub hdisj hcell0
  refine hmain.trans ?_
  have hres : W \ ⋃ i ∈ (↑S : Set _), c i = Sigma \
      ⋃ r ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n Sigma r,
        adaptedCellAt q r w := by
    dsimp only [W, S, c, Sigma, R]
    rw [union_hybrid_family hZp hZ]
    ext x
    simp only [hybridStrip, Set.mem_sdiff, Set.mem_union]
    tauto
  rw [hres]
  have hsum : ∑ i ∈ S, (volume (c i)).toReal / (volume W).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X)) =
      (∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal /
          (volume W).toReal * (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
        ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
          (volume (adaptedCellAt q r w)).toReal / (volume W).toReal *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X)) := by
    dsimp only [S, R, c, W]
    rw [Finset.sum_disjSum]
    exact congrArg (fun t => _ + t) (sum_hybrid_rows _)
  rw [hsum]

end

end Transport
end HighContrast
end Homogenization
