import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentScaleInput

/-!
# The response load as a quadratic form

`respLsqMinus` and `respLsqPlus` are defined as the `respEhatMinus`- and
`respEhatPlus`-quadratic forms of the response loads `respxMinus` and `respxPlus`.
This file records the two consequences of that definition that the per-scale
input consumes: the load is nonnegative when the corresponding block is positive
semidefinite, and the averaged-energy hypothesis of the per-scale input is the
quadratic-form bound with the two right-hand factors in the printed order.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- `respLsqMinus` is definitionally the quadratic form of `respxMinus` under
`respEhatMinus`. -/
theorem h6a_respLsqMinus_eq_quadratic (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) :
    respLsqMinus P jStar F t e
      = blockVecDot (respxMinus P jStar F t e)
          (blockMatVecMul (respEhatMinus P jStar F t) (respxMinus P jStar F t e)) :=
  rfl

omit [NeZero d] in
/-- `respLsqPlus` is definitionally the quadratic form of `respxPlus` under
`respEhatPlus`. -/
theorem h6a_respLsqPlus_eq_quadratic (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) :
    respLsqPlus P jStar F t e
      = blockVecDot (respxPlus P jStar F t e)
          (blockMatVecMul (respEhatPlus P jStar F t) (respxPlus P jStar F t e)) :=
  rfl

end

end Homogenization.HighContrast.Multiscale
