import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakScaleEnergy

/-!
# The composed per-scale tail bound

At depth `n` the older-scale tail of the cell-average estimate compares the transported recentred
subcell averages of the doubled optimizer field with the transported parent cell average.  This
module composes the per-scale energy bound `h6a_scaleEnergy_of_analytic` with the two remaining
analytic inputs:

* the variance bound `hvar`, which majorizes the recentred flat `L²` average by the uncentred one;
* the per-cell energy bound `hcell` and the parent partition identity `hpart`, which supply the
  averaged energy bound of the spine.

The result is the tail estimate `√(card⁻¹ ∑ |R((X)_w − (X)_U)|²) ≤ √2 · K · B · ℰ`, where `ℰ` is
the pathwise optimizer energy of the parent adapted cell.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The composed per-scale tail bound.**  Suppose the recentred flat `L²` average of the
transported subcell averages is at most the uncentred one, each transported subcell average
satisfies the quadratic bound against `(K B)^2` times twice its subcell energy average, and the flat
average of the subcell energy averages equals the squared parent pathwise energy `ℰ^2`.  Then the
transported recentred tail is at most `√2 · K · B · ℰ`. -/
theorem h6a_scaleTail_of_inputs (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (b : CoeffField d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hvar : ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (optimizerField b u) -
                cellAverage (HighContrast.adaptedCell q t) (optimizerField b u)))
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (optimizerField b u) -
                cellAverage (HighContrast.adaptedCell q t) (optimizerField b u)))
        ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u)))
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u))))
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)))
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)))
        ≤ (K * B) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)))
    (hpart : ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      = weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u) -
              cellAverage (HighContrast.adaptedCell q t) (optimizerField b u)))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u) -
              cellAverage (HighContrast.adaptedCell q t) (optimizerField b u))))
      ≤ Real.sqrt 2 * K * B * weakOptimizerEnergy (HighContrast.adaptedCell q t) b u := by
  have henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      ≤ 2 * weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2 := by
    have heq : ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
        = 2 * (((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)) := by
      rw [← Finset.mul_sum]
      ring
    rw [heq, hpart]
  have hunc : Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        blockVecDot
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (optimizerField b u)))
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (optimizerField b u))))
      ≤ Real.sqrt 2 * K * B * weakOptimizerEnergy (HighContrast.adaptedCell q t) b u :=
    h6a_scaleEnergy_of_analytic q t n R (fun _ => optimizerField b u)
      (fun w => 2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2))
      K B (weakOptimizerEnergy (HighContrast.adaptedCell q t) b u)
      hK hB (Real.sqrt_nonneg _) hcell henergy
  exact le_trans (Real.sqrt_le_sqrt hvar) hunc

end

end Homogenization.HighContrast.Multiscale
