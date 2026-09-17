import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage
import HCPoly.Entry.Annealed.AlignedSubdivision

/-!
# Refining a weighted flat cell average by one triadic generation

The descendant telescoping of `p.response.transfer` compares the cutoff cell averages at two
consecutive generations.  The bookkeeping it needs is that a flat average over the depth-`m`
subcells of the terminal cell, of a weight `c w` against the cell average of a fixed integrable
function `f`, is unchanged when each depth-`m` cell is refined into its `3 ^ d` children: the
weight is then read at the parent index.

```
avg_{w ∈ box m}  c w · ⨍_{V^m_w} f  =  avg_{W ∈ box (m+1)}  c (parent W) · ⨍_{V^{m+1}_W} f.
```

The proof uses only the landed partition of the centred terminal cell
(`avsum_volumeAverage_eq`), applied once at depth `m` and once at depth `m + 1`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- **The parent of a cell of the triadic box lies in the coarser box.**  If `W` indexes a cell
of depth `m + 1` inside the terminal cell, its parent index of depth `m` indexes a cell of the
same terminal cell. -/
theorem parentIndex_mem_triadicIndexBox {d m : ℕ} {W : Fin d → ℤ}
    (hW : W ∈ triadicIndexBox d (m + 1)) :
    Geometry.parentIndex W ∈ triadicIndexBox d m := by
  rw [triadicIndexBox, Fintype.mem_piFinset] at hW ⊢
  intro i
  have hWi := hW i
  rw [Finset.mem_Icc] at hWi ⊢
  simp only [Geometry.parentIndex]
  obtain ⟨k, hk⟩ : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
  have hkdiv : ((3 : ℕ) ^ m - 1) / 2 = k := by
    have hm1 : (3 : ℕ) ^ m - 1 = 2 * k := by omega
    rw [hm1, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  have hk1 : (3 : ℕ) ^ (m + 1) = 2 * (3 * k + 1) + 1 := by
    rw [pow_succ, hk]; ring
  have hk1div : ((3 : ℕ) ^ (m + 1) - 1) / 2 = 3 * k + 1 := by
    have hm1 : (3 : ℕ) ^ (m + 1) - 1 = 2 * (3 * k + 1) := by omega
    rw [hm1, Nat.mul_div_cancel_left (3 * k + 1) (by norm_num : 0 < 2)]
  have hbm : ((((3 : ℕ) ^ m - 1) / 2 : ℕ) : ℤ) = (k : ℤ) := by exact_mod_cast hkdiv
  have hbm1 : ((((3 : ℕ) ^ (m + 1) - 1) / 2 : ℕ) : ℤ) = ((3 * k + 1 : ℕ) : ℤ) := by
    exact_mod_cast hk1div
  rw [hbm1] at hWi
  rw [hbm] at ⊢
  constructor
  · rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 3)]
    omega
  · rw [Int.ediv_le_iff_le_mul (by norm_num : (0 : ℤ) < 3)]
    omega

/-- **A triadic cell sits in its parent.**  The aligned adapted cell of generation `k` at index
`W` is contained in the aligned adapted cell of generation `k + 1` at the parent index. -/
theorem adaptedCellAtCenter_subset_parent {d : ℕ} (q : Mat d) (k : ℤ) (W : Fin d → ℤ) :
    adaptedCellAtCenter q k W ⊆ adaptedCellAtCenter q (k + 1) (Geometry.parentIndex W) := by
  simp only [Geometry.adaptedCellAtCenter_eq_affine_standardCell]
  exact Set.image_mono (Geometry.standardCell_subset_parent k W)

/-- **The children of one triadic cell carry its cell average.**  Summing the cell averages of
`f` over the depth-`(m+1)` cells whose parent index is `w`, normalised by the number of
depth-`(m+1)` cells, gives the cell average of `f` over the depth-`m` cell at `w`, normalised by
the number of depth-`m` cells. -/
theorem avsum_fiber_volumeAverage_eq {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (m : ℕ) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d m) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ *
        ∑ W ∈ (triadicIndexBox d (m + 1)).filter
            (fun W => Geometry.parentIndex W = w),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f
      = ((triadicIndexBox d m).card : ℝ)⁻¹ *
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
  classical
  set g : Vec d → ℝ := Set.indicator (adaptedCellAtCenter q (t - (m : ℤ)) w) f with hgdef
  have hVmeas : MeasurableSet (adaptedCellAtCenter q (t - (m : ℤ)) w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (m : ℤ)) w).measurableSet
  have hg : IntegrableOn g (HighContrast.adaptedCell q t) := by
    rw [hgdef]
    exact hf.indicator hVmeas
  have hpart_m := avsum_volumeAverage_eq q hq t m hg
  have hpart_m1 := avsum_volumeAverage_eq q hq t (m + 1) hg
  have hpart := hpart_m.trans hpart_m1.symm
  have hzero_V : ∀ v : Fin d → ℤ, v ≠ w →
      volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g = 0 := by
    intro v hv
    rw [volumeAverage]
    have hzero : ∫ x in adaptedCellAtCenter q (t - (m : ℤ)) v, g x = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      rw [hgdef]
      exact Set.indicator_of_notMem
        (Set.disjoint_left.mp (Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (m : ℤ)) hv) hx) f
    rw [hzero, mul_zero]
  have hcollapse_m : (∑ v ∈ triadicIndexBox d m,
        volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g)
      = volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
    calc ∑ v ∈ triadicIndexBox d m, volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g
        = volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) g :=
          Finset.sum_eq_single (s := triadicIndexBox d m)
            (f := fun v => volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g)
            w (fun v _ hvne => hzero_V v hvne) (fun hnot => absurd hw hnot)
      _ = volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
          rw [volumeAverage, volumeAverage]
          congr 1
          apply setIntegral_congr_fun hVmeas
          intro x hx
          rw [hgdef]
          exact Set.indicator_of_mem hx f
  have heq_W : ∀ W ∈ triadicIndexBox d (m + 1), Geometry.parentIndex W = w →
      volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g
        = volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
    intro W _ hp
    rw [volumeAverage, volumeAverage]
    congr 1
    apply setIntegral_congr_fun (isOpen_adaptedCellAtCenter_of_isUnit hq _ W).measurableSet
    intro x hx
    rw [hgdef]
    refine Set.indicator_of_mem ?_ f
    have hsub : adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W ⊆
        adaptedCellAtCenter q (t - (m : ℤ)) w := by
      have h := adaptedCellAtCenter_subset_parent q (t - ((m + 1 : ℕ) : ℤ)) W
      rw [hp] at h
      rw [show t - ((m + 1 : ℕ) : ℤ) + 1 = t - (m : ℤ) by push_cast; ring] at h
      exact h
    exact hsub hx
  have hzero_W : ∀ W ∈ triadicIndexBox d (m + 1), Geometry.parentIndex W ≠ w →
      volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g = 0 := by
    intro W hW hne
    rw [volumeAverage]
    have hzero : ∫ x in adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W, g x = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      rw [hgdef]
      refine Set.indicator_of_notMem ?_ f
      have hsub : adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W ⊆
          adaptedCellAtCenter q (t - (m : ℤ)) (Geometry.parentIndex W) := by
        have h := adaptedCellAtCenter_subset_parent q (t - ((m + 1 : ℕ) : ℤ)) W
        rw [show t - ((m + 1 : ℕ) : ℤ) + 1 = t - (m : ℤ) by push_cast; ring] at h
        exact h
      exact Set.disjoint_left.mp
        (Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (m : ℤ)) hne) (hsub hx)
    rw [hzero, mul_zero]
  have hfilter := Finset.sum_filter_of_ne
      (s := triadicIndexBox d (m + 1))
      (p := fun W => Geometry.parentIndex W = w)
      (f := fun W => volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g)
      (fun W hW hne => by
        by_contra hp
        exact hne (hzero_W W hW hp))
  have hcollapse_m1 : (∑ W ∈ triadicIndexBox d (m + 1),
        volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g)
      = ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
    calc ∑ W ∈ triadicIndexBox d (m + 1),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g
        = ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g := hfilter.symm
      _ = ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
          refine Finset.sum_congr rfl ?_
          intro W hW
          exact heq_W W (Finset.mem_filter.mp hW).1 (Finset.mem_filter.mp hW).2
  calc ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ *
        (∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
      = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ *
          (∑ W ∈ triadicIndexBox d (m + 1),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g) := by
        rw [← hcollapse_m1]
    _ = ((triadicIndexBox d m).card : ℝ)⁻¹ *
          (∑ v ∈ triadicIndexBox d m,
            volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g) := hpart.symm
    _ = ((triadicIndexBox d m).card : ℝ)⁻¹ *
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by rw [hcollapse_m]

/-- **Refining a weighted flat cell average by one generation.**  The flat average over the
depth-`m` subcells of a weight against the cell average of `f` equals the flat average over the
depth-`(m+1)` subcells of the same weight read at the parent index. -/
theorem avsum_weighted_volumeAverage_succ_eq {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (m : ℕ) (c : (Fin d → ℤ) → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d m).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d m,
        c w * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
      = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
          c (Geometry.parentIndex W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
  classical
  set A : ℝ := ((triadicIndexBox d m).card : ℝ)⁻¹ with hA
  set B : ℝ := ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ with hB
  have hfiber : (∑ w ∈ triadicIndexBox d m,
        ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
          c (Geometry.parentIndex W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
      = ∑ W ∈ triadicIndexBox d (m + 1),
          c (Geometry.parentIndex W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f :=
    Finset.sum_fiberwise_of_maps_to
      (s := triadicIndexBox d (m + 1)) (t := triadicIndexBox d m)
      (g := Geometry.parentIndex)
      (fun W hW => parentIndex_mem_triadicIndexBox hW)
      (fun W => c (Geometry.parentIndex W)
        * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
  have hstep3 : ∀ w ∈ triadicIndexBox d m,
      B * (∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
        = A * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
    intro w hw
    have h := avsum_fiber_volumeAverage_eq (q := q) hq t m w hw (f := f) hf
    rw [hB, hA]
    exact h
  have hfilter_eq : ∀ w ∈ triadicIndexBox d m,
      (∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
          c (Geometry.parentIndex W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
        = c w * (∑ W ∈ (triadicIndexBox d (m + 1)).filter
              (fun W => Geometry.parentIndex W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f) := by
    intro w _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro W hW
    rw [(Finset.mem_filter.mp hW).2]
  calc A * ∑ w ∈ triadicIndexBox d m,
        c w * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
      = ∑ w ∈ triadicIndexBox d m,
          c w * (A * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
    _ = ∑ w ∈ triadicIndexBox d m,
          c w * (B * (∑ W ∈ (triadicIndexBox d (m + 1)).filter
                (fun W => Geometry.parentIndex W = w),
              volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)) := by
        refine Finset.sum_congr rfl ?_
        intro w hw
        rw [← hstep3 w hw]
    _ = B * ∑ w ∈ triadicIndexBox d m,
          c w * (∑ W ∈ (triadicIndexBox d (m + 1)).filter
                (fun W => Geometry.parentIndex W = w),
              volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
    _ = B * ∑ w ∈ triadicIndexBox d m,
          ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Geometry.parentIndex W = w),
            c (Geometry.parentIndex W)
              * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro w hw
        rw [← hfilter_eq w hw]
    _ = B * ∑ W ∈ triadicIndexBox d (m + 1),
          c (Geometry.parentIndex W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
        rw [hfiber]

end

end Homogenization.HighContrast.Multiscale
