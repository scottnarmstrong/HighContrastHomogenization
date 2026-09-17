import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentScaleInput

/-!
# The plus twin of the per-scale analytic input

`h6a_scaleInput_of_analytic_plus` is the adjoint (`a_+`) twin of
`h6a_scaleInput_of_analytic` (`HC2b_DiagonalWeakRecentScaleInput.lean`): the per-scale input of
the cell-average lemma with the response sample replaced by `respEhatPlus`, `respLsqPlus` and
`respCoeffPlus`.  The algebraic spine `h6a_scaleInput_spine_le` is sign-free and is reused
unchanged, so the two analytic inputs keep exactly the same shape with the plus sample.
-/

open Homogenization.HighContrast (CoeffSpace normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The adjoint (`a_+`) twin of `h6a_scaleInput_of_analytic`.

The index set is `triadicIndexBox d n`, the root is `blockSqrt (respM0 F)`, and the scalars are
the plus ones: `√(blockSpecBound (normalizedBlock (respEhatPlus …) (respM0 F)))`, the all-scale
maximum factor `1 + √(respAllScaleMax …) · 3^{ρn/2}`, `√(respLsqPlus …)`, and the block size of
`weakAverageDefect … (respEhatPlus …) (respCoeffPlus …)`.  The per-cell hypothesis `hcell` and
the averaged energy hypothesis `henergy` are transported verbatim from the minus statement. -/
theorem h6a_scaleInput_of_analytic_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (a : CoeffSpace d) (n : ℕ)
    (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ)
    (hLsq : 0 ≤ respLsqPlus P jStar F t e)
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 * G w)
    (henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
      ≤ 2 * respLsqPlus P jStar F t e
          * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
              (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqPlus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖ := by
  have hB : (0 : ℝ) ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) :=
    add_nonneg zero_le_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hLsq' : Real.sqrt (respLsqPlus P jStar F t e) ^ 2 = respLsqPlus P jStar F t e :=
    Real.sq_sqrt hLsq
  refine h6a_scaleInput_spine_le (triadicIndexBox d n) (blockSqrt (respM0 F))
    (fun w => cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)) G
    _ _ _ _ (Real.sqrt_nonneg _) hB (Real.sqrt_nonneg _) (norm_nonneg _) hcell ?_
  rw [hLsq']
  exact henergy

end

end Homogenization.HighContrast.Multiscale
