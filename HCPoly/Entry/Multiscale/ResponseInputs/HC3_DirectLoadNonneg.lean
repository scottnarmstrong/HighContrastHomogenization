import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# Nonnegativity of the source load and the cutoff error-row arithmetic

The source load `L_s^±` of `p.response.transfer` is a weighted sum of squares against
nonnegative weights, hence nonnegative.  The cutoff estimate `e.response.cutoff.estimate`
collects its three error rows and the cutoff pairing term under one constant by elementary
arithmetic, using only that every scalar in sight is nonnegative.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The source load `L_s` is nonnegative: it is a sum over scales of a nonnegative weight
`3 ^ (-(3/2) n)` times a cell average of a squared sum of square roots. -/
theorem zero_le_respSourceLoad {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    0 ≤ respSourceLoad P jStar F s b Y := by
  unfold respSourceLoad
  exact tsum_nonneg fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun z _ => sq_nonneg _))

/-- `L_s^-` is nonnegative, being the source load of the recentred coefficient `a_-`. -/
theorem zero_le_respLsMinus {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) :
    0 ≤ respLsMinus P jStar F s t e := by
  unfold respLsMinus
  exact zero_le_respSourceLoad P jStar F s (respCoeffMinus F) (respYMinus P jStar F t e)

/-- `L_s^+` is nonnegative, being the source load of the adjoint recentred coefficient `a_+`. -/
theorem zero_le_respLsPlus {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (e : Vec d) :
    0 ≤ respLsPlus P jStar F s t e := by
  unfold respLsPlus
  exact zero_le_respSourceLoad P jStar F s (respCoeffPlus F) (respYPlus P jStar F t e)

end

end Homogenization.HighContrast.Multiscale
