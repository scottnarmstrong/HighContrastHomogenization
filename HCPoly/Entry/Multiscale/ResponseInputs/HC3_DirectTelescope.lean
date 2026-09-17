import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectNest
import HCPoly.Entry.Annealed.MeanOrder
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportEnergies
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportRows
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsPartitionCell

/-!
# The descendant telescoping of the cutoff cell weights

Refining the depth-`m` subdivision of the terminal cell into the depth-`(m+1)` subdivision turns
the difference of the two weighted flat cell averages of the cutoff cell weights against the cell
averages of a fixed integrable field into the flat average of the weight increment against the
finer cell averages.  Summing those increments over the generations telescopes the depth-`N`
weighted flat average into the terminal depth-zero term plus the descendant sum that
`p.response.transfer` bounds.
-/

open Homogenization.HighContrast (adaptedCellCenter)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- **The increment of the weighted flat cell average across one generation.**  Refining the
depth-`m` subdivision into the depth-`(m+1)` subdivision turns the difference of the two weighted
flat averages into the flat average of the weight increment against the finer cell averages. -/
theorem avsum_weighted_volumeAverage_succ_sub {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (m : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f
        - ((triadicIndexBox d m).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d m,
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
      = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
          (volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
              - volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) (Geometry.parentIndex W))
                  (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
  have h :
      ((triadicIndexBox d m).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d m,
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
        = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
            volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) (Geometry.parentIndex W))
                (fun x => φ x - 1)
              * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f :=
    avsum_weighted_volumeAverage_succ_eq (q := q) hq t m
      (fun v => volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) (fun x => φ x - 1))
      (f := f) hf
  rw [h, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro W _
  ring

/-- **The weighted flat cell average telescopes over the generations.**  The depth-`N` weighted
flat average of the cutoff cell weights against the cell averages of `f` is the terminal term
plus the sum of the generation increments.  For a cutoff of the class `IsResponseCutoff` the
terminal term vanishes, so the whole quantity is the descendant sum of
`p.response.transfer`. -/
theorem avsum_weighted_volumeAverage_eq_sum_range {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (N : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d N).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d N,
          volumeAverage (adaptedCellAtCenter q (t - (N : ℤ)) W) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (N : ℤ)) W) f
      = volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x - 1)
            * volumeAverage (HighContrast.adaptedCell q t) f
        + ∑ m ∈ Finset.range N,
            ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
              (volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
                  - volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) (Geometry.parentIndex W))
                      (fun x => φ x - 1))
                * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
  induction N with
  | zero =>
      have hbox0 : triadicIndexBox d 0 = {(0 : Fin d → ℤ)} := by
        unfold triadicIndexBox
        have hfun : (fun _ : Fin d => Finset.Icc (-(((3 ^ 0 - 1) / 2 : ℕ) : ℤ))
            (((3 ^ 0 - 1) / 2 : ℕ) : ℤ)) = (fun _ : Fin d => ({(0 : ℤ)} : Finset ℤ)) := by
          funext i
          simp
        rw [hfun]
        exact Fintype.piFinset_singleton (fun _ : Fin d => (0 : ℤ))
      have hcell0 : adaptedCellAtCenter q t (0 : Fin d → ℤ) = HighContrast.adaptedCell q t := by
        have hc : adaptedCellCenter q t (0 : Fin d → ℤ) = 0 := by
          rw [adaptedCellCenter]
          have h0 : (fun i => (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = (0 : Vec d) := by
            funext i
            simp
          rw [h0, matVecMul_zero, smul_zero]
        rw [adaptedCellAtCenter, hc]
        simp only [HighContrast.adaptedCellTranslate, zero_add, Set.image_id']
      rw [Finset.sum_range_zero, add_zero, hbox0]
      simp only [Finset.card_singleton, Nat.cast_one, inv_one, one_mul,
        Finset.sum_singleton, Nat.cast_zero, sub_zero, hcell0]
  | succ N ih =>
      have h := avsum_weighted_volumeAverage_succ_sub (q := q) hq t N φ hf
      simp only [Finset.sum_range_succ]
      rw [← add_assoc, ← ih, ← h]
      ring

end

end Homogenization.HighContrast.Multiscale
