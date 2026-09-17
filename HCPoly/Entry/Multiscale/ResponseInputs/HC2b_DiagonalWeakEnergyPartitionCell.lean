import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakEnergyPartition
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCellCover

/-!
# The parent optimizer energy partition at the adapted cells

The partition identity recombines the flat average of the depth-`n` subcell energy averages
into the squared pathwise optimizer energy of the parent adapted cell.  In its general form
that identity carries nine geometric and integrability hypotheses.  For the aligned adapted
cells every geometric one of them is supplied by `IsUnit q` and the tree's cell lemmas: the
subcells are open hence measurable, pairwise disjoint, contained in the parent, omit only the
null grid seams, and have equal volume, and the parent cell has positive finite volume.  This
file discharges those hypotheses and lands the clean statement.

The nonnegativity of the averaged doubled-optimizer density and its integrability are not
available from `IsUnit q` alone: the coefficient field is an arbitrary matrix-valued field, so
`x ↦ (X x).1 · (X x).2` need not be nonnegative and need not be integrable.  They remain
explicit hypotheses rather than being replaced by a stronger ellipticity assumption.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The parent optimizer energy partition at the adapted cells.**  For an invertible grid
`q`, generation `t` and depth `n`, the flat average over the `3^{nd}` aligned depth-`n`
subcells of their averaged doubled-optimizer energy densities equals the squared pathwise
normalized optimizer energy of the parent adapted cell `HighContrast.adaptedCell q t`.  Every
geometric and finiteness hypothesis of the general partition identity is discharged from
`IsUnit q`; only the nonnegativity and the integrability of the averaged density remain as
hypotheses. -/
theorem h6a_parent_energy_partition_cell (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    (b : CoeffField d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hnn : 0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2))
    (hint : IntegrableOn
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      = weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2 := by
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
  exact h6a_parent_energy_partition q t n b u hnn
    (fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet)
    (fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww')
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (h6a_adaptedCell_diff_biUnion_null q hq t n)
    (fun w _ => h6a_volume_adaptedCellAtCenter_card_eq q hq t n w)
    hint hUpos hUfin

end

end Homogenization.HighContrast.Multiscale
