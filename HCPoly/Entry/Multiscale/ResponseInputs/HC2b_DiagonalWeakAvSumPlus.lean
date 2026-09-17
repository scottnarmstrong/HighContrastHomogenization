import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentAvSum

/-!
# The averaged-defect window sum for the adjoint sample

This is the plus twin of the averaged-defect window sum `h6a_weakAverageSum_half_le`.  The
per-scale bound on the abstract family `A : ℕ → ℝ` is the same good-branch coefficient
`√2 (1 + √M · 3^{ρ n/2})`, and the window summation is the same arithmetic on the geometric
weights `3^{-n/2}` and `3^{-(1/2 - ρ/2)n}`.  The only change is the sample: the recentred field
`a_- = respCoeffMinus F a` and the response matrix `E_-^t = respEhatMinus P jStar F t` are
replaced by their adjoint counterparts `a_+ = respCoeffPlus F a` and
`E_+^t = respEhatPlus P jStar F t`.  This is the averaged-defect summand of the weak-norm
estimate `e.response.weak.estimate`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **`e.response.weak.estimate`, averaged-defect window sum for the adjoint sample.**  For the
adjoint sample `a_+ = respCoeffPlus F a`, the adjoint response matrix
`E_+^t = respEhatPlus P jStar F t`, and a family `A : ℕ → ℝ` bounded per scale by the
good-branch coefficient `√2 (1 + √M · 3^{ρ n/2})` against the averaged recent-defect size
`‖weakAverageDefect · E_+^t · a_+‖`, the `3^{-n/2}`-weighted sum over the window `n ≤ H` is
bounded by `4 K L` times the printed weighted averaged-defect sum
`∑ 3^{-(1/2 - ρ/2)n} ‖weakAverageDefect · E_+^t · a_+‖`.

`M = respAllScaleMax P γ jStar F t a` is assumed at most `1` (the nondegenerate branch), `K` and
`L` are nonnegative, and `_hE` records that the adjoint response matrix `E_+^t` is positive
definite; the latter is the nondegeneracy condition carried by the route. -/
theorem h6a_weakAverageSum_half_le_plus (P : Measure (CoeffSpace d)) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) (A : ℕ → ℝ)
    (_hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 * K *
        (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
          (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) * L *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) :
    ∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n ≤
      4 * K * L *
        weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
          (respCoeffPlus F a) := by
  have hrho0 : 0 ≤ respRho γ := (h6a_respRho_pos hγ).le
  refine h6a_weakAverageSum_window_le (K := 4 * K) (L := L) _ t H (respRho γ) _ _
    (fun n => (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n) ?_
  intro n _
  set M : ℝ := respAllScaleMax P γ jStar F t a with hM
  set R : ℝ := (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) with hR
  set W : ℝ := (3 : ℝ) ^ (-((n : ℝ) / 2)) with hW
  set D : ℝ := Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
    (respEhatPlus P jStar F t) (respCoeffPlus F a))‖ with hD
  have hR1 : (1 : ℝ) ≤ R := h6a_one_le_recentWeight hrho0 n
  have hW0 : (0 : ℝ) ≤ W := Real.rpow_nonneg (by norm_num) _
  have hD0 : (0 : ℝ) ≤ D := Real.sqrt_nonneg _
  have hrest0 : (0 : ℝ) ≤ K * L * D := mul_nonneg (mul_nonneg hK0 hL0) hD0
  have hcoeff : Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 4 * R := h6a_avCoeff_le hgood hR1
  have hstep : A n ≤ (4 * R) * (K * L * D) := by
    refine (hscale n).trans ?_
    calc
      Real.sqrt 2 * K * (1 + Real.sqrt M * R) * L * D
          = (Real.sqrt 2 * (1 + Real.sqrt M * R)) * (K * L * D) := by ring
      _ ≤ (4 * R) * (K * L * D) := mul_le_mul_of_nonneg_right hcoeff hrest0
  calc
    W * A n ≤ W * ((4 * R) * (K * L * D)) := mul_le_mul_of_nonneg_left hstep hW0
    _ = 4 * K * L * ((W * R) * D) := by ring
    _ = 4 * K * L * ((3 : ℝ) ^ (-((1 / 2 : ℝ) - respRho γ / 2) * (n : ℝ)) * D) := by
        rw [hW, hR, h6a_recentWeight_mul]

end

end Homogenization.HighContrast.Multiscale
