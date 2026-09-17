import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# The depth-`n` subcells cover their parent adapted cell up to a null set

The cells `adaptedCellAtCenter q (t - n) w` over the index box `triadicIndexBox d n` are `3^{nd}`
pairwise disjoint open subcells of the parent `HighContrast.adaptedCell q t`.  They omit the
interior seams, so they are not literally a cover, but the omitted set is Lebesgue-null.
The three facts proved here are the volume bookkeeping (`card` times a subcell volume equals
the parent volume), the equality of the union with the parent at the level of measures, and
the nullity of the difference.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The volume of any depth-`n` subcell, multiplied by the number of subcells, is the volume
of the parent cell.  The identity is purely translation invariance of Lebesgue measure plus
the scale arithmetic `3^{nd} · 3^{(t-n)d} = 3^{td}`. -/
theorem h6a_volume_adaptedCellAtCenter_card_eq (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    (w : Fin d → ℤ) :
    ((triadicIndexBox d n).card : ℝ) * (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
      = (volume (HighContrast.adaptedCell q t)).toReal := by
  have hdet : |q.det| ≠ 0 :=
    abs_ne_zero.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det q).mp hq))
  have h3 : (3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ)) = (3 : ℝ) ^ t := by
    rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast (3 : ℝ) n).symm,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hmain : ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d = ((3 : ℝ) ^ t) ^ d := by
    rw [← mul_pow, h3]
  have hVreal : (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
      = |q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
  rw [card_triadicIndexBox, hVreal, Geometry.volume_adaptedCell_toReal]
  exact mul_left_cancel₀ hdet (by rw [← hmain]; ring)

/-- The union of the depth-`n` subcells has the same volume as the parent cell.  The union is
an a.e. cover, and the equality follows from finite additivity over the pairwise disjoint
measurable subcells together with the per-cell volume identity. -/
theorem h6a_volume_biUnion_adaptedCellAtCenter (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ) :
    volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      = volume (HighContrast.adaptedCell q t) := by
  classical
  have hmeas : ∀ w ∈ triadicIndexBox d n,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
  have hdisj : Set.PairwiseDisjoint (↑(triadicIndexBox d n) : Set (Fin d → ℤ))
      (fun w => adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    intro a _ b _ hab
    exact Geometry.adaptedCellAtCenter_disjoint_of_ne hq _ hab
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hconst : ∀ w, volume (adaptedCellAtCenter q (t - (n : ℤ)) w)
      = volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := by
    intro w
    simp only [Geometry.volume_adaptedCellAtCenter]
  have hsum : ∑ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) w)
      = ((triadicIndexBox d n).card : ℝ≥0∞)
          * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := by
    calc ∑ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) w)
        = ∑ _w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) :=
          Finset.sum_congr rfl (fun w _ => hconst w)
      _ = ((triadicIndexBox d n).card : ℝ≥0∞)
            * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := h6a_volume_adaptedCellAtCenter_card_eq q hq t n 0
  have hEnn : ((triadicIndexBox d n).card : ℝ≥0∞)
        * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0)
      = volume (HighContrast.adaptedCell q t) := by
    refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) 0)
    · exact hUfin
    · rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      exact hcard
  calc volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      = ∑ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
        measure_biUnion_finset hdisj hmeas
    _ = ((triadicIndexBox d n).card : ℝ≥0∞)
          * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := hsum
    _ = volume (HighContrast.adaptedCell q t) := hEnn

/-- The parent cell differs from the union of its depth-`n` subcells by a null set.  This is
the a.e. covering statement: the union is measurable, contained in the parent, and has the
same (finite) measure, so the difference is null. -/
theorem h6a_adaptedCell_diff_biUnion_null (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ) :
    volume (HighContrast.adaptedCell q t \
        ⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) = 0 := by
  classical
  have hsub : (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      ⊆ HighContrast.adaptedCell q t := by
    refine Set.iUnion₂_subset ?_
    intro w hw
    exact adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hOpen : IsOpen (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_iUnion fun w => isOpen_iUnion fun _ => isOpen_adaptedCellAtCenter_of_isUnit hq _ w
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hVeq : volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      = volume (HighContrast.adaptedCell q t) :=
    h6a_volume_biUnion_adaptedCellAtCenter q hq t n
  have hVfin : volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ := by
    rw [hVeq]
    exact hUfin
  rw [measure_sdiff hsub hOpen.measurableSet.nullMeasurableSet hVfin, hVeq]
  simp

end

end Homogenization.HighContrast.Multiscale
