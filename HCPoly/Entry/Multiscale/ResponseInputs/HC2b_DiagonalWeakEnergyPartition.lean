import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakPartitionAE
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# The parent optimizer energy recombines over the depth-`n` subcells

The pathwise normalized optimizer energy `weakOptimizerEnergy U b u` is the square root of the
average of the doubled-optimizer energy density `x ↦ (X x).1 · (X x).2`, where `X = optimizerField
b u` is the doubled optimizer field.  The first statement below squares that definition: on a
region where the average is nonnegative, squaring the energy recovers the average.

The second statement is the partition identity that lets the per-cell energy map recombine into
the parent energy.  When the parent adapted cell is the almost-everywhere disjoint union of its
`3^{nd}` aligned depth-`n` subcells, all of them of equal volume, the *unweighted* flat average of
the subcell energy averages is the parent average.  The equal-volume hypothesis is what makes the
unweighted mean correct; without it the recombination would have to be the volume-weighted sum
`∑_w (|V w| / |U|) ⨍_{V w} g`.  It is stated through `.toReal`, and together with the positivity of
the parent volume it excludes a zero-volume subcell: a zero-volume cell would force the left side
of `hvolw` to vanish while the right side is positive.  The almost-everywhere partition step itself
is `h6a_average_over_aePartition`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Squaring the pathwise normalized optimizer energy recovers the average of the doubled field's
energy density, as soon as that average is nonnegative. -/
theorem h6a_sq_weakOptimizerEnergy {U : Set (Vec d)} (b : CoeffField d)
    (u : AHarmonicFunction b U)
    (hnn : 0 ≤ volumeAverage U (fun x => vecDot (optimizerField b u x).1
      (optimizerField b u x).2)) :
    weakOptimizerEnergy U b u ^ 2
      = volumeAverage U (fun x => vecDot (optimizerField b u x).1
      (optimizerField b u x).2) :=
  Real.sq_sqrt hnn

omit [NeZero d] in
/-- **The parent optimizer energy recombines over the depth-`n` subcells.**  Under the
almost-everywhere partition hypotheses, the flat average over the `3^{nd}` aligned depth-`n`
subcells of their energy averages is the squared pathwise optimizer energy of the parent adapted
cell. -/
theorem h6a_parent_energy_partition (q : Mat d) (t : ℤ) (n : ℕ) (b : CoeffField d)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hnn : 0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2))
    (hmeas : ∀ w ∈ triadicIndexBox d n,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hdisj : ∀ w ∈ triadicIndexBox d n, ∀ w' ∈ triadicIndexBox d n, w ≠ w' →
      Disjoint (adaptedCellAtCenter q (t - (n : ℤ)) w) (adaptedCellAtCenter q (t - (n : ℤ)) w'))
    (hsub : ∀ w ∈ triadicIndexBox d n,
      adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t)
    (hnull : volume (HighContrast.adaptedCell q t \
        ⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) = 0)
    (hvolw : ∀ w ∈ triadicIndexBox d n,
      ((triadicIndexBox d n).card : ℝ) * (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
        = (volume (HighContrast.adaptedCell q t)).toReal)
    (hint : IntegrableOn
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      (HighContrast.adaptedCell q t))
    (hUpos : 0 < (volume (HighContrast.adaptedCell q t)).toReal)
    (hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      = weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2 := by
  have hZne : (triadicIndexBox d n).Nonempty := by
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hmain := h6a_average_over_aePartition (Z := triadicIndexBox d n)
    (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
    (U := HighContrast.adaptedCell q t)
    (g := fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
    hmeas hdisj hsub hnull hvolw hint hUpos hUfin hZne
  rw [h6a_sq_weakOptimizerEnergy (U := HighContrast.adaptedCell q t) b u hnn]
  exact hmain

end

end Homogenization.HighContrast.Multiscale
