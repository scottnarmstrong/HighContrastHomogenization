import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectTelescope

/-!
# The oscillation decomposition of the cutoff-mean row

The oscillation half of the cutoff-mean row of `p.response.transfer` compares the
`(φ - 1)`-weighted average of an integrable density `f` over the terminal cell with its depth-`H`
cell part.  Refining the subdivision generation by generation, that difference is the sum of the
generation increments of the descendant sum, carried by the deeper cells, plus the defect of the
farthest cell part.  The telescoping identity at every depth produces both readings once it is
subtracted from itself at the shifted depth.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The shifted descendant telescoping.**  The difference between the depth-`(H+N)` and the
depth-`H` weighted flat cell averages is the sum of the `N` generation increments below the
scale-`s` cells, the depth-`n` increment being carried by the generation `t - (H + n + 1)`. -/
theorem avsum_weighted_volumeAverage_add_sub_eq_sum_range {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (H N : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + N),
          volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) f
        - ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) f
      = ∑ n ∈ Finset.range N,
          ((triadicIndexBox d (H + n + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + n + 1),
            (volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
                - volumeAverage (adaptedCellAtCenter q (t - ((H + n : ℕ) : ℤ))
                    (Geometry.parentIndex W)) (fun x => φ x - 1))
              * volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) f := by
  have hHN := avsum_weighted_volumeAverage_eq_sum_range (q := q) hq t (H + N) φ hf
  have hH := avsum_weighted_volumeAverage_eq_sum_range (q := q) hq t H φ hf
  rw [hHN, hH, Finset.sum_range_add]
  ring

/-- **The oscillation decomposition of the cutoff-mean row at every refinement depth.**  The
`(φ-1)`-weighted average of `f` over the terminal cell is its depth-`H` cell part, plus the first
`N` generation increments of the descendant sum of `p.response.transfer`, plus a remainder which
is the defect of the depth-`(H+N)` cell part. -/
theorem volumeAverage_sub_one_eq_cellPart_add_sum_range_add_rem {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (H N : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * f x)
      = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) (fun x => φ x - 1)
              * volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) f
        + (∑ n ∈ Finset.range N,
            ((triadicIndexBox d (H + n + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + n + 1),
              (volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
                  - volumeAverage (adaptedCellAtCenter q (t - ((H + n : ℕ) : ℤ))
                      (Geometry.parentIndex W)) (fun x => φ x - 1))
                * volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) f)
        + (volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * f x)
            - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + N),
                volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) (fun x => φ x - 1)
                  * volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) f) := by
  rw [← avsum_weighted_volumeAverage_add_sub_eq_sum_range hq t H N φ hf]
  ring

end

end Homogenization.HighContrast.Multiscale
