import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakEnergyPartitionCell

/-!
# Exact partition averaging on the adapted cell

The cell decomposition used in the response cutoff estimate first replaces the average over the
adapted cell `HighContrast.adaptedCell q t` by the flat average of the normalized averages over its
`3^{nd}` triadic subcells `adaptedCellAtCenter q (t - n) w`, `w ∈ triadicIndexBox d n`.  Unlike the
recombination of the optimizer energy, this step needs neither positivity of the integrand nor a
bound on it: the parent cell is the disjoint union of its open subcells up to the null grid seams,
the subcells have equal volume, and the identity follows from finite additivity of the integral.
This file records the index box nonemptiness used to normalize the finite sum and the exact
averaging identity itself.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The triadic index box of generation `n` is nonempty: the constant index `0` has every
coordinate in the interval `[-(3^n - 1)/2, (3^n - 1)/2]`. -/
theorem triadicIndexBox_nonempty (d : ℕ) [NeZero d] (n : ℕ) : (triadicIndexBox d n).Nonempty := by
  refine ⟨0, ?_⟩
  rw [triadicIndexBox, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_Icc.mpr
    ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩

/-- **Exact partition averaging on the adapted cell** (`e.response.cutoff.estimate`).  For an
invertible grid `q`, generation `t` and depth `n`, the normalized average of an integrand `g`
over the adapted cell `HighContrast.adaptedCell q t` is the flat average of the normalized averages
of `g` over the `3^{nd}` triadic subcells `adaptedCellAtCenter q (t - n) w`.  Only the integrability of
`g` on the parent cell is needed; the subcells cover the parent up to the null grid seams, and
their equal volumes make the unweighted mean the correct recombination. -/
theorem volumeAverage_adaptedCell_eq_flat_average {d : ℕ} [NeZero d] (q : Mat d)
    (hq : IsUnit q) (t : ℤ) (n : ℕ) (g : Vec d → ℝ)
    (hint : IntegrableOn g (HighContrast.adaptedCell q t)) :
    volumeAverage (HighContrast.adaptedCell q t) g
      = ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n, volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g := by
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
  exact (h6a_average_over_aePartition (Z := triadicIndexBox d n)
    (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
    (U := HighContrast.adaptedCell q t) (g := g)
    (fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet)
    (fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww')
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (h6a_adaptedCell_diff_biUnion_null q hq t n)
    (fun w _ => h6a_volume_adaptedCellAtCenter_card_eq q hq t n w)
    hint hUpos hUfin (triadicIndexBox_nonempty d n)).symm

end

end Homogenization.HighContrast.Multiscale
