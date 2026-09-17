import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsLoadHead

/-!
# The depth-zero head of the source load

The cell half of the cutoff-mean row of `p.response.transfer` pairs the mean defect against the
dual variable `Y` and produces the square of the two-term head
`(|b_s^{1/2}P| + |(S_{*,s})^{-1/2}Q|)` of the source load at the terminal generation's own
scale.  The source load `L_s` is the sum over the descendant generations of `3^{-3n/2}` times the
flat average of the same expression, so the head is the `n = 0` summand of that sum and is
therefore at most `L_s` as soon as the family is summable.  This module exposes that terminal
summand and bounds the head by the load.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The terminal (`n = 0`) summand of the source load `L_s` of `p.response.transfer`: at
generation `0` the weight `3^{-3n/2}` is `1`, the triadic index box is the singleton box `{0}`,
and the flat average collapses to the value at the scale-`s` cell itself, so the summand is
exactly the squared two-term head `(|b_s^{1/2}P| + |(S_{*,s})^{-1/2}Q|)²`. -/
theorem respSourceLoadSummand_zero {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    respSourceLoadSummand P jStar F s b Y 0
      = (Real.sqrt (vecDot Y.1 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).lowerRight Y.2))) ^ 2 := by
  unfold respSourceLoadSummand
  rw [triadicIndexBox_zero d]
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul, Finset.card_singleton,
    Nat.cast_one, inv_one, Finset.sum_singleton, sub_zero]

/-- The squared two-term head `(|b_s^{1/2}P| + |(S_{*,s})^{-1/2}Q|)²` at the terminal scale is
the `n = 0` summand of the source load `L_s` of `p.response.transfer`, so whenever the defining
series converges the head is at most the load itself. -/
theorem sq_head_le_respSourceLoad {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hsum : Summable (respSourceLoadSummand P jStar F s b Y)) :
    (Real.sqrt (vecDot Y.1 (matVecMul
          (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
          (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s 0) b).lowerRight Y.2))) ^ 2
      ≤ respSourceLoad P jStar F s b Y := by
  rw [respSourceLoad_eq_tsum_summand]
  rw [← respSourceLoadSummand_zero P jStar F s b Y]
  exact hsum.le_tsum 0 (fun n _ => respSourceLoad_summand_nonneg P jStar F s b Y n)

end

end Homogenization.HighContrast.Multiscale
