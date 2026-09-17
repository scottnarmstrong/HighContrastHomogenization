import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentAssembly

/-!
# The metric factor of the normalized response block, adjoint sign

For a positive definite numerator and a positive definite normalizer, the spectral positive
part of the normalized block is the whole matrix, so its one-sided spectral bound coincides
with its operator norm.  This file records that coincidence for the adjoint response
`respEhatPlus`, the sign that is paired with `respxPlus` in the weak-norm estimate: the
metric factor printed there equals the one delivered by the cell-sum half.
-/

open Homogenization.HighContrast (CoeffSpace normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The spectral bound of the `respEhatPlus`-normalized response block equals its operator
norm, because both `respEhatPlus P jStar F t` and the normalizer `respM0 F` are positive
definite. -/
theorem h6a_respK0_specBound_eq_norm_plus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)) =
      ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ :=
  h6a_blockSpecBound_normalizedBlock_eq_norm _ _ hE hM0

end

end Homogenization.HighContrast.Multiscale
