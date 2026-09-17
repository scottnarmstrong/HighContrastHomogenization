import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentScaleInput

/-!
# The per-cell hypothesis of the per-scale input, from its two inputs

The per-scale input `h6a_scaleInput_of_analytic` consumes a per-cell hypothesis bounding the
metric square of a cell average by a fixed printed constant times a weight `G`.  The energy-map
layer delivers that bound with a different constant: a product `k * e` of two Loewner sizes.
This file is the bookkeeping that turns the second shape into the first, given the numerical
comparison between the two constants.

Both statements are monotonicity of multiplication by a nonnegative weight.  No matrix identity
is used beyond the nonnegativity of the quantities involved, and the first statement is the
generic core of the second.
-/

open Homogenization.HighContrast (CoeffSpace normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-- Monotonicity of a per-cell bound in its constant.  If `V w ≤ c₁ * G w` for every `w` in a
finite index set and the weight `G` is nonnegative there, then the same bound holds with any
larger constant `c₂`.  The nonnegativity of `c₁` is carried because the constant in the analytic
per-scale input is a product of Loewner sizes, but the monotonicity step itself needs only
`c₁ ≤ c₂` and `0 ≤ G w`. -/
theorem h6a_hcell_of_constants {iota : Type*} (Z : Finset iota) (V : iota → ℝ) (G : iota → ℝ)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hG : ∀ w ∈ Z, 0 ≤ G w) (hcc : c₁ ≤ c₂)
    (hmetric : ∀ w ∈ Z, V w ≤ c₁ * G w) :
    ∀ w ∈ Z, V w ≤ c₂ * G w := by
  have _ := hc₁
  intro w hw
  exact le_trans (hmetric w hw) (mul_le_mul_of_nonneg_right hcc (hG w hw))

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The per-cell hypothesis of the per-scale input, obtained from the energy-map bound.  The
cell-average metric square is bounded by `(k * e) * G w` for the two Loewner sizes `k` and `e`;
the comparison `hsize` turns the product into the printed square
`(√K₀ · (1 + √M · 3^{ρn/2}))²`, and the nonnegative weight yields the conclusion.  The index set
is `triadicIndexBox d n`, the root is `blockSqrt (respM0 F)`, and the two constants and the
response sample are those of the weak-norm estimate (`e.response.weak.estimate`). -/
theorem h6a_hcell_of_metric_and_size
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    (n : ℕ) (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ) (k e : ℝ)
    (hk : 0 ≤ k) (he : 0 ≤ e)
    (hG : ∀ w ∈ triadicIndexBox d n, 0 ≤ G w)
    (hsize : k * e ≤
      (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2)
    (hmetric : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (k * e) * G w) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 * G w := by
  exact h6a_hcell_of_constants (triadicIndexBox d n)
    (fun w => blockVecDot
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w))))
    G (k * e)
    ((Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2)
    (mul_nonneg hk he) hG hsize hmetric

end

end Homogenization.HighContrast.Multiscale
