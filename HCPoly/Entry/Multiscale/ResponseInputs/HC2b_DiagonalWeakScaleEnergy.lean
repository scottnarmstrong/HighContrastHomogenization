import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentScaleInput

/-!
# The per-scale energy bound

The head/tail splitting of the normalized scale-average seminorm leaves a single per-scale
estimate: the normalized `L²` average, over the depth-`n` aligned subcells, of the metric transport
of the recentred cell averages of a doubled field is bounded by `√2 · K · B · ℰ`, where `ℰ` is the
pathwise optimizer energy of the parent adapted cell.

The algebraic content is the real-arithmetic spine `h6a_scaleInput_spine_le`, which combines a
per-cell quadratic bound with an averaged energy bound.  This module specializes that spine to the
parent optimizer energy: the averaged energy bound is the partition identity that recombines the
subcell energy averages into the squared parent energy, so the energy factor in the conclusion is
the parent pathwise energy itself.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The per-scale energy bound, from a per-cell bound and an averaged energy bound.**  If every
depth-`n` subcell `adaptedCellAtCenter q (t - n) w` bounds the quadratic metric form of the transported
cell average `R (X)_w` by `(K B)^2` times a nonnegative energy density `G w`, and if the flat
average of `G` over the subcells is at most `2 En^2`, then the flat `L²` average of the transported
cell averages is at most `√2 · K · B · En`.

This is the spine `h6a_scaleInput_spine_le` at load `En` and defect `1`; the factor `√1 = 1` is
discarded. -/
theorem h6a_scaleEnergy_of_analytic (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ) (K B En : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hEn : 0 ≤ En)
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)))
        ≤ (K * B) ^ 2 * G w)
    (henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
      ≤ 2 * En ^ 2) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w))))
      ≤ Real.sqrt 2 * K * B * En := by
  have h := h6a_scaleInput_spine_le (triadicIndexBox d n) R
    (fun w => cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)) G K B En 1
    hK hB hEn zero_le_one hcell (by simpa only [mul_one] using henergy)
  simpa only [Real.sqrt_one, mul_one] using h

end

end Homogenization.HighContrast.Multiscale
