import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakScaleTail
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakVarianceBound
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakParentMean

/-!
# The per-scale older-scale bound at the estimate's own carriers

The cell-average estimate `e.response.weak.estimate` controls, at each depth `n`, the normalized
`L²` average over the aligned depth-`n` subcells of the recentred transported subcell averages of
the doubled optimizer field, by `√2 · K · B · ℰ`.  Here `K` is the square root of the spectral
bound of the normalized block, `B = 1 + √M · 3^{ρ n / 2}` combines the all-scale maximum `M` with
the geometric window weight, and `ℰ` is the pathwise optimizer energy of the parent adapted cell.

This module specializes the generic composed bound `h6a_scaleTail_of_inputs` to the estimate's own
carriers: the selected grid `respGrid`, the parent cell `respCell`, the metric transport
`blockSqrt (respM0 F)`, the coefficient field `respCoeffMinus F a`, and the optimizer field of the
parent.  The three analytic inputs are supplied generically: the variance step
`h6a_scaleTerm_centred_le` fed with the parent-mean identity
`h6a_cellAverage_parent_eq_avg_subcells`, the per-cell quadratic bound `hcell` (a hypothesis), and
the parent energy partition `h6a_parent_energy_partition_cell`.
-/

open Homogenization.HighContrast (CoeffSpace normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The per-scale older-scale bound at the estimate's own carriers.**  For an invertible selected
grid, a generation `t`, a depth `n` and a parent harmonic optimizer, if every aligned depth-`n`
subcell bounds the quadratic metric form of its transported cell average by `(K B)^2` times twice
its energy average, then the normalized `L²` average of the recentred transported subcell averages
is at most `√2 · K · B · ℰ`, where `K = √(‖(Ehat_t^-)_+‖)` and `B = 1 + √M · 3^{ρ n / 2}`.  The
parent-mean identity and the parent energy partition are discharged internally from `IsUnit q`; the
integrability and nonnegativity of the parent energy density remain explicit hypotheses. -/
theorem h6a_scaleTail_carrier (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
              (optimizerField (respCoeffMinus F a) u x).2)))
    (h1 : ∀ j : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).1 j) (respCell jStar F t))
    (h2 : ∀ j : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).2 j) (respCell jStar F t))
    (hnn : 0 ≤ volumeAverage (respCell jStar F t)
      (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
        (optimizerField (respCoeffMinus F a) u x).2))
    (hintE : IntegrableOn
      (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
        (optimizerField (respCoeffMinus F a) u x).2) (respCell jStar F t)) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u := by
  have hmean := h6a_cellAverage_parent_eq_avg_subcells (respGrid jStar F) hgrid t n
    (optimizerField (respCoeffMinus F a) u) h1 h2
  have hvar := h6a_scaleTerm_centred_le (respGrid jStar F) t n (blockSqrt (respM0 F))
    (optimizerField (respCoeffMinus F a) u) hmean.1 hmean.2
  have hpart := h6a_parent_energy_partition_cell (respGrid jStar F) hgrid t n
    (respCoeffMinus F a) u hnn hintE
  have hK : 0 ≤
      Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) :=
    Real.sqrt_nonneg _
  have hB : 0 ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) := by
    have hs : 0 ≤ Real.sqrt (respAllScaleMax P γ jStar F t a) := Real.sqrt_nonneg _
    have hp : 0 ≤ (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    linarith only [mul_nonneg hs hp]
  exact h6a_scaleTail_of_inputs (respGrid jStar F) t n (blockSqrt (respM0 F))
    (respCoeffMinus F a) u
    (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))))
    (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))
    hK hB hvar hcell hpart

end

end Homogenization.HighContrast.Multiscale
