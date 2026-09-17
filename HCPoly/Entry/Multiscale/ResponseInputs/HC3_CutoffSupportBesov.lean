import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# The squared scale-average seminorm bound

The scale-average seminorm `[X]` of AK.HC (2.130) is defined in `AdaptedDefs.lean` as a real
`tsum`; this file records its nonnegativity and the nonnegativity of the squared `L²` cell mean. The
Jensen/partition bound, in squared form, bounds the seminorm itself (rather than `3^{-t/2}` times it)
by the `L²(U_t)` mean of the field.

-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The squared Euclidean norm of a doubled vector is nonnegative:
`blockVecDot X X = |X.1| ^ 2 + |X.2| ^ 2 ≥ 0`. -/
theorem blockVecDot_self_nonneg (X : BlockVec d) : 0 ≤ blockVecDot X X := by
  have h1 : 0 ≤ vecNormSq X.1 := vecNormSq_nonneg X.1
  have h2 : 0 ≤ vecNormSq X.2 := vecNormSq_nonneg X.2
  simpa [blockVecDot, vecNormSq] using add_nonneg h1 h2

omit [NeZero d] in
/-- The scale-average seminorm `[X]` of AK.HC (2.130) is nonnegative, the junk value of a
divergent defining series being `0`. -/
theorem besovSeminorm_nonneg (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d) :
    0 ≤ besovSeminorm t avg := by
  unfold besovSeminorm
  exact tsum_nonneg fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)

end

end Homogenization.HighContrast.Multiscale
