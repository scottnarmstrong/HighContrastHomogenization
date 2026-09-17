import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real arithmetic for the weak-estimate assembly

This leaf module collects the purely real identities and inequalities that are used when
the weak-norm estimate is assembled from its pieces.  Nothing here mentions a measure, a
matrix, a block or a function space: every statement is an identity or an inequality
between real numbers.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- Three-term Cauchy–Schwarz: `(x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2)`. -/
theorem h612_add3_sq_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-- `(3 ^ (-(t / 2))) ^ 2 = 3 ^ (-t)` for the real power. -/
theorem h612_rpow_half_sq (t : ℝ) : ((3 : ℝ) ^ (-(t / 2))) ^ 2 = (3 : ℝ) ^ (-t) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    show -(t / 2) * ((2 : ℕ) : ℝ) = -t by ring]

/-- Square of a product of two square roots:
`(c * √x * √y * s) ^ 2 = c ^ 2 * (x * y) * s ^ 2`. -/
theorem h612_sqrt_mul_sq (c x y s : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (c * Real.sqrt x * Real.sqrt y * s) ^ 2 = c ^ 2 * (x * y) * s ^ 2 := by
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]
  ring

/-- Square of a scaled square root: `(c * √v) ^ 2 = c ^ 2 * v`. -/
theorem h612_scaled_sqrt_sq (c v : ℝ) (hv : 0 ≤ v) : (c * Real.sqrt v) ^ 2 = c ^ 2 * v := by
  rw [mul_pow, Real.sq_sqrt hv]

/-- `3 ^ (-(1 / 2)) < 1`, hence `0 < 1 - 3 ^ (-(1 / 2))`. -/
theorem h612_one_sub_rpow_pos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
  sub_pos.mpr <| Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- `(η ^ (1 / (2 * Q))) ^ 2 = η ^ (1 / Q)` for `η ≥ 0` and `Q > 0`. -/
theorem h612_rpow_sq_eq (η : ℝ) (hη : 0 ≤ η) (Q : ℝ) (hQ : 0 < Q) :
    (η ^ ((1 : ℝ) / (2 * Q))) ^ 2 = η ^ ((1 : ℝ) / Q) := by
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have h2Qne : (2 : ℝ) * Q ≠ 0 := mul_ne_zero (by norm_num) hQne
  have hexp : (1 : ℝ) / (2 * Q) * ((2 : ℕ) : ℝ) = 1 / Q := by
    field_simp [hQne, h2Qne]
    ring
  rw [← Real.rpow_natCast, ← Real.rpow_mul hη, hexp]

/-- For `0 < η ≤ 1` the exponent map is antitone, so `η ^ (2 / Q) ≤ η ^ (1 / Q)`. -/
theorem h612_rpow_two_le_one (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (Q : ℝ) (hQ : 0 < Q) :
    η ^ ((2 : ℝ) / Q) ≤ η ^ ((1 : ℝ) / Q) :=
  Real.rpow_le_rpow_of_exponent_ge hη0 hη1
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hQ.le)

/-- Final constant bookkeeping for the weak estimate.  If `X ≤ (A * z ^ 2 + B * θ ^ 2) * κ`
and all of `A`, `B`, `θ`, `z`, `κ` are nonnegative, then
`X ≤ (√(B + 1) * (θ + √(A + 1) * z) * √κ) ^ 2`. -/
theorem h612_constant_arith (A B θ z κ X : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 ≤ θ)
    (hz : 0 ≤ z) (hκ : 0 ≤ κ) (hX : X ≤ (A * z ^ 2 + B * θ ^ 2) * κ) :
    X ≤ (Real.sqrt (B + 1) * (θ + Real.sqrt (A + 1) * z) * Real.sqrt κ) ^ 2 := by
  have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
  have hsB : (Real.sqrt (B + 1)) ^ 2 = B + 1 := Real.sq_sqrt hB1
  have hsA : (Real.sqrt (A + 1)) ^ 2 = A + 1 := Real.sq_sqrt hA1
  have hsk : (Real.sqrt κ) ^ 2 = κ := Real.sq_sqrt hκ
  have hsAs : (0 : ℝ) ≤ Real.sqrt (A + 1) := Real.sqrt_nonneg _
  have hcross : (0 : ℝ) ≤ 2 * (B + 1) * θ * (Real.sqrt (A + 1) * z) := by
    have h : (0 : ℝ) ≤ (B + 1) * θ * (Real.sqrt (A + 1) * z) :=
      mul_nonneg (mul_nonneg hB1 hθ) (mul_nonneg hsAs hz)
    nlinarith [h]
  have hBA : (0 : ℝ) ≤ B * A * z ^ 2 := mul_nonneg (mul_nonneg hB hA) (sq_nonneg z)
  have hBz : (0 : ℝ) ≤ B * z ^ 2 := mul_nonneg hB (sq_nonneg z)
  have hkey : A * z ^ 2 + B * θ ^ 2 ≤ (B + 1) * (θ + Real.sqrt (A + 1) * z) ^ 2 := by
    nlinarith [hsA, sq_nonneg θ, hcross, hBA, hBz, sq_nonneg z, hsAs, hA, hB, hθ, hz]
  have hmain : (A * z ^ 2 + B * θ ^ 2) * κ
      ≤ ((B + 1) * (θ + Real.sqrt (A + 1) * z) ^ 2) * κ :=
    mul_le_mul_of_nonneg_right hkey hκ
  calc
    X ≤ (A * z ^ 2 + B * θ ^ 2) * κ := hX
    _ ≤ ((B + 1) * (θ + Real.sqrt (A + 1) * z) ^ 2) * κ := hmain
    _ = (Real.sqrt (B + 1) * (θ + Real.sqrt (A + 1) * z) * Real.sqrt κ) ^ 2 := by
          rw [mul_pow, mul_pow, hsB, hsk]

end

end Homogenization.HighContrast.Multiscale
