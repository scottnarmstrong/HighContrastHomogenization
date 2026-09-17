import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar arithmetic for the first error row

The first error row of `p.response.transfer` is assembled by integrating a pointwise bound
`|E - J| ≤ D + 2 √(J D)`.  Because the square root carries no measurability hypothesis, the
integrand is replaced by the one-parameter family `2 √(J D) ≤ ε J + D / ε`, integrated for each
`ε > 0`, and optimized only at the end.  This module supplies the scalar inequalities behind that
replacement together with the subadditivity that turns `√(τ (E + τ))` into `√(τ E) + τ`.

* `two_mul_sqrt_mul_le_eps_add_div` — the one-parameter Young bound on the cross term.
* `le_add_two_mul_sqrt_of_forall_pos` — optimization of the parameter at the end.
* `sqrt_mul_add_le_sqrt_mul_add` — splitting the terminal-scale annealed response.

Paper: the first error row of `p.response.transfer`.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- Young's inequality in the product form used for the cross term: for `J, D ≥ 0` and `ε > 0`,
`2 √(J D) ≤ ε J + D / ε`. -/
theorem two_mul_sqrt_mul_le_eps_add_div (J D ε : ℝ) (hJ : 0 ≤ J) (hD : 0 ≤ D) (hε : 0 < ε) :
    2 * Real.sqrt (J * D) ≤ ε * J + D / ε := by
  have hε0 : 0 ≤ ε := hε.le
  have hεJ : 0 ≤ ε * J := mul_nonneg hε0 hJ
  have hDε : 0 ≤ D / ε := div_nonneg hD hε0
  have harg : (ε * J) * (D / ε) = J * D := by
    field_simp [hε.ne']
  have hsqrt : Real.sqrt (J * D) = Real.sqrt (ε * J) * Real.sqrt (D / ε) := by
    rw [← Real.sqrt_mul hεJ (D / ε), harg]
  calc 2 * Real.sqrt (J * D)
      = 2 * Real.sqrt (ε * J) * Real.sqrt (D / ε) := by rw [hsqrt]; ring
    _ ≤ Real.sqrt (ε * J) ^ 2 + Real.sqrt (D / ε) ^ 2 := two_mul_le_add_sq _ _
    _ = ε * J + D / ε := by rw [Real.sq_sqrt hεJ, Real.sq_sqrt hDε]

/-- Optimizing the one-parameter family: if `X ≤ B + ε A + T / ε` for every `ε > 0` and
`A, T ≥ 0`, then `X ≤ B + 2 √(T A)`. -/
theorem le_add_two_mul_sqrt_of_forall_pos (X B A T : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (h : ∀ ε : ℝ, 0 < ε → X ≤ B + (ε * A + T / ε)) :
    X ≤ B + 2 * Real.sqrt (T * A) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · subst hA0
    simp only [mul_zero, Real.sqrt_zero, add_zero]
    rcases eq_or_lt_of_le hT with hT0 | hTpos
    · subst hT0
      simpa using h 1 one_pos
    · apply le_of_forall_pos_le_add
      intro δ hδ
      have hε : 0 < T / δ := div_pos hTpos hδ
      calc X ≤ B + ((T / δ) * 0 + T / (T / δ)) := h (T / δ) hε
        _ = B + δ := by field_simp [hTpos.ne', hδ.ne']; ring
  · rcases eq_or_lt_of_le hT with hT0 | hTpos
    · subst hT0
      simp only [zero_mul, Real.sqrt_zero, mul_zero, add_zero]
      apply le_of_forall_pos_le_add
      intro δ hδ
      have hε : 0 < δ / A := div_pos hδ hApos
      calc X ≤ B + ((δ / A) * A + 0 / (δ / A)) := h (δ / A) hε
        _ = B + δ := by field_simp [hApos.ne', hδ.ne']; ring
    · have hTA : 0 ≤ T * A := mul_nonneg hTpos.le hApos.le
      have hTA' : 0 ≤ T / A := div_nonneg hTpos.le hApos.le
      have hε : 0 < Real.sqrt (T / A) := Real.sqrt_pos.2 (div_pos hTpos hApos)
      have hA1 : Real.sqrt (T / A) * A = Real.sqrt (T * A) := by
        calc Real.sqrt (T / A) * A
            = Real.sqrt (T / A) * Real.sqrt (A ^ 2) := by rw [Real.sqrt_sq hApos.le]
          _ = Real.sqrt ((T / A) * A ^ 2) := (Real.sqrt_mul hTA' (A ^ 2)).symm
          _ = Real.sqrt (T * A) := by
                congr 1
                field_simp [hApos.ne']
      have hA2 : T / Real.sqrt (T / A) = Real.sqrt (T * A) := by
        rw [div_eq_iff hε.ne']
        calc T = Real.sqrt (T ^ 2) := (Real.sqrt_sq hTpos.le).symm
          _ = Real.sqrt ((T * A) * (T / A)) := by
                congr 1
                field_simp [hApos.ne']
          _ = Real.sqrt (T * A) * Real.sqrt (T / A) := Real.sqrt_mul hTA (T / A)
      calc X ≤ B + (Real.sqrt (T / A) * A + T / Real.sqrt (T / A)) := h _ hε
        _ = B + 2 * Real.sqrt (T * A) := by rw [hA1, hA2]; ring

/-- The terminal-scale splitting of the annealed response: for `A, T ≥ 0`,
`√(T (A + T)) ≤ √(T A) + T`. -/
theorem sqrt_mul_add_le_sqrt_mul_add (A T : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T) :
    Real.sqrt (T * (A + T)) ≤ Real.sqrt (T * A) + T := by
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) hT)]
  have hTA : 0 ≤ T * A := mul_nonneg hT hA
  have hsq : (Real.sqrt (T * A) + T) ^ 2
      = T * (A + T) + 2 * (T * Real.sqrt (T * A)) := by
    rw [add_sq, Real.sq_sqrt hTA]
    ring
  rw [hsq]
  have hnonneg : 0 ≤ 2 * (T * Real.sqrt (T * A)) :=
    mul_nonneg (by norm_num) (mul_nonneg hT (Real.sqrt_nonneg _))
  exact le_add_of_nonneg_right hnonneg

end

end Homogenization.HighContrast.Multiscale
