import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarmH5Abs

/-!
# The source load dominates its own scale-`m` term

The source load `L_s` of `e.response.cutoff.estimate` is the sum over generations of the
weighted flat averages of the squared `(b_{s-n,z}, S_{*,s-n,z})`-norms of the annealed mean.
Every one of its summands is nonnegative, so whenever the series converges it dominates each of
its terms -- in particular the terminal term `m = 0`, which is the flat average over the
terminal partition that the cutoff-mean rows pair against.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Every summand of the source load `L_s` of `e.response.cutoff.estimate` is nonnegative: the
geometric weight `3^{-3n/2}` is positive, the reciprocal cell count is nonnegative, and the
inner average is a sum of squares. -/
theorem respSourceLoad_summand_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) (n : ℕ) :
    0 ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2) := by
  refine mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun z _ => sq_nonneg _)

end

end Homogenization.HighContrast.Multiscale
