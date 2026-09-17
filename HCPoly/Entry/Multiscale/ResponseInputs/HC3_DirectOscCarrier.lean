import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscWeight
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectNest
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCutoffWeights

/-!
# The descendant weight of the cutoff-mean row at the carriers

The descendant sum of `p.response.transfer` runs over the generations below the scale-`s` cells,
i.e. over the depths `H + n + 1` of the terminal cell.  Its weight at depth `H + n + 1` is the
increment of the cutoff cell averages between a cell and the cell of the previous generation
containing it.  The cutoff class bounds that increment by `32 d² Θ 3^{-(H+n)}`, which is the shape
`K · 3^{-n}` the descendant row consumes, with `K = 32 d² Θ 3^{-H}` carrying the printed factor
`3^{-H}`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The descendant weight of the cutoff-mean row.**  At the generation `t - (H + n + 1)` the
increment of the cutoff cell averages between a cell and its parent is at most
`(32 d² Θ 3^{-H}) · 3^{-n}`.  This is the weight of the depth-`n` term of the descendant sum of
`p.response.transfer`. -/
theorem abs_cutoff_weight_increment_le {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq) {t : ℤ}
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (H n : ℕ) (W : Fin d → ℤ) :
    |volumeAverage (adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ)) (Geometry.parentIndex W))
            (fun x => φ x - 1)|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(n : ℝ)) := by
  have hsub : adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W ⊆
      adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ)) (Geometry.parentIndex W) := by
    have h := adaptedCellAtCenter_subset_parent qq (t - ((H + n + 1 : ℕ) : ℤ)) W
    simpa only [show t - ((H + n + 1 : ℕ) : ℤ) + 1 = t - ((H + n : ℕ) : ℤ) by
      push_cast; ring] using h
  have hPpos :
      0 < (volume (adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ))
        (Geometry.parentIndex W))).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - ((H + n : ℕ) : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det qq).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - ((H + n : ℕ) : ℤ))) d)
  have hWpos :
      0 < (volume (adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W)).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - ((H + n + 1 : ℕ) : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det qq).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - ((H + n + 1 : ℕ) : ℤ))) d)
  have hmain := abs_volumeAverage_sub_one_sub_volumeAverage_sub_one_le (d := d) (qq := qq)
    hq (t := t) (φ := φ) hφ (H + n) (Geometry.parentIndex W)
    (W := adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W)
    hsub (ne_of_gt hPpos) (Geometry.volume_adaptedCellAtCenter_ne_top qq _ _)
    (integrableOn_isResponseCutoff hq hφ _ _)
    (ne_of_gt hWpos) (Geometry.volume_adaptedCellAtCenter_ne_top qq _ _)
    (integrableOn_isResponseCutoff hq hφ _ _)
  have hpow : (3 : ℝ) ^ (-(((H + n : ℕ) : ℝ))) =
      (3 : ℝ) ^ (-(H : ℝ)) * (3 : ℝ) ^ (-(n : ℝ)) := by
    rw [show -(((H + n : ℕ) : ℝ)) = -(H : ℝ) + -(n : ℝ) by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  calc
    |volumeAverage (adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ)) (Geometry.parentIndex W))
            (fun x => φ x - 1)|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst *
            (3 : ℝ) ^ (-(((H + n : ℕ) : ℝ))) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(n : ℝ)) := by
        rw [hpow]; ring

end

end Homogenization.HighContrast.Multiscale
