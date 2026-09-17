import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakEnergyPartitionCell

/-!
# The parent cell average of a doubled field is the flat average of its subcell averages

For an invertible grid `q`, a generation `t` and a depth `n`, the `3^{nd}` aligned depth-`n`
subcells `adaptedCellAtCenter q (t - n) w` are pairwise disjoint open sets of equal volume, contained
in the parent cell `HighContrast.adaptedCell q t`, and covering it up to the Lebesgue-null grid
seams.  Consequently, for a doubled field `X` whose components are integrable on the parent
cell, the flat average over the index box of the subcell averages of each component equals the
parent cell average of that component.

This is the vector-valued counterpart of the scalar parent energy partition: each component of
`cellAverage` is a scalar `volumeAverage`, and the whole statement is `2 d` instances of the
almost-everywhere partition identity `h6a_average_over_aePartition`.  The equal volume of the
subcells is what makes the unweighted flat mean correct; a weighted sum would be needed without
it.  Measurability, disjointness, containment and the null seam are all supplied by `IsUnit q`
through the cell lemmas, while the integrability of each component is an explicit hypothesis.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The parent cell average is the flat average of the subcell averages.**  For an invertible
grid `q`, generation `t` and depth `n`, each component of the parent cell average of a doubled
field `X` over `HighContrast.adaptedCell q t` equals the flat average over the `3^{nd}` aligned
depth-`n` subcells of that component's subcell averages.  Every geometric hypothesis is
discharged from `IsUnit q`; only the integrability of the two components on the parent cell
remains as a hypothesis. -/
theorem h6a_cellAverage_parent_eq_avg_subcells (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    (X : Vec d → BlockVec d)
    (h1 : ∀ j : Fin d, IntegrableOn (fun x => (X x).1 j) (HighContrast.adaptedCell q t))
    (h2 : ∀ j : Fin d, IntegrableOn (fun x => (X x).2 j) (HighContrast.adaptedCell q t)) :
    (∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).1 i
      = (cellAverage (HighContrast.adaptedCell q t) X).1 i) ∧
    (∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).2 i
      = (cellAverage (HighContrast.adaptedCell q t) X).2 i) := by
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hUpos : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hZne : (triadicIndexBox d n).Nonempty := by
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hmeas : ∀ w ∈ triadicIndexBox d n,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hdisj : ∀ w ∈ triadicIndexBox d n, ∀ w' ∈ triadicIndexBox d n, w ≠ w' →
      Disjoint (adaptedCellAtCenter q (t - (n : ℤ)) w) (adaptedCellAtCenter q (t - (n : ℤ)) w') :=
    fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww'
  have hsub : ∀ w ∈ triadicIndexBox d n,
      adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hnull : volume (HighContrast.adaptedCell q t \
      ⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) = 0 :=
    h6a_adaptedCell_diff_biUnion_null q hq t n
  have hvolw : ∀ w ∈ triadicIndexBox d n,
      ((triadicIndexBox d n).card : ℝ)
          * (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
        = (volume (HighContrast.adaptedCell q t)).toReal :=
    fun w _ => h6a_volume_adaptedCellAtCenter_card_eq q hq t n w
  constructor
  · intro i
    have hi := h6a_average_over_aePartition (Z := triadicIndexBox d n)
      (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
      (U := HighContrast.adaptedCell q t) (g := fun x => (X x).1 i)
      hmeas hdisj hsub hnull hvolw (h1 i) hUpos hUfin hZne
    simpa only [cellAverage] using hi
  · intro i
    have hi := h6a_average_over_aePartition (Z := triadicIndexBox d n)
      (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
      (U := HighContrast.adaptedCell q t) (g := fun x => (X x).2 i)
      hmeas hdisj hsub hnull hvolw (h2 i) hUpos hUfin hZne
    simpa only [cellAverage] using hi

end

end Homogenization.HighContrast.Multiscale
