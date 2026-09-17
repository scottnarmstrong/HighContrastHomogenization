import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weighted flat averages over the cells of a partition

The first error row of `e.response.cutoff.estimate` averages over the scale-`s` subcells of a
terminal cell.  The cutoff fluctuations about one are bounded by one in absolute value, so the
weighted flat average of the fluctuation times an integrand is controlled by the flat average of
the absolute integrand; the cross terms are then averaged by the discrete Cauchy--Schwarz
inequality for flat averages.  This file records those two finite-sum steps, together with the
additivity of the flat average.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- **Weighted flat average against a bounded weight.**  If every weight `fl w` is bounded in
absolute value by one on the finite index set `Z`, then the flat average of `fl w * v w` is
bounded by the flat average of `|v w|`.  The weight bound enters pointwise through
`|fl w * v w| ≤ |v w|`, and the nonnegative factor `(Z.card : ℝ)⁻¹` passes through the resulting
sum inequality.  This is the weighted cell step of `e.response.cutoff.estimate`. -/
theorem abs_flat_average_weighted_le {iota : Type*} (Z : Finset iota) (fl v : iota → ℝ)
    (hfl : ∀ w ∈ Z, |fl w| ≤ 1) :
    |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, fl w * v w| ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w| := by
  have hc : 0 ≤ (Z.card : ℝ)⁻¹ := by positivity
  have hS : |∑ w ∈ Z, fl w * v w| ≤ ∑ w ∈ Z, |v w| := by
    calc
      |∑ w ∈ Z, fl w * v w| ≤ ∑ w ∈ Z, |fl w * v w| :=
        Finset.abs_sum_le_sum_abs (fun w => fl w * v w) Z
      _ = ∑ w ∈ Z, |fl w| * |v w| :=
        Finset.sum_congr rfl fun w _ => abs_mul (fl w) (v w)
      _ ≤ ∑ w ∈ Z, 1 * |v w| :=
        Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_right (hfl w hw) (abs_nonneg (v w))
      _ = ∑ w ∈ Z, |v w| := by simp
  calc
    |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, fl w * v w|
        = (Z.card : ℝ)⁻¹ * |∑ w ∈ Z, fl w * v w| := by
          rw [abs_mul, abs_of_nonneg hc]
    _ ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w| := mul_le_mul_of_nonneg_left hS hc

/-- **Discrete Cauchy--Schwarz for flat averages.**  If `x` and `y` are nonnegative on `Z`, the
flat average of `√(x w) * √(y w)` is bounded by the product of the square roots of the flat
averages of `x` and of `y`.  The Cauchy--Schwarz inequality for finite sums gives the unnormalized
bound, and multiplying by the nonnegative factor `(Z.card : ℝ)⁻¹` turns the product of the two
square roots into the product of the normalized square roots.  This controls the cross terms of
the optimizer replacement in `e.response.cutoff.estimate`. -/
theorem flat_average_sqrt_mul_sqrt_le {iota : Type*} (Z : Finset iota) (x y : iota → ℝ)
    (hx : ∀ w ∈ Z, 0 ≤ x w) (hy : ∀ w ∈ Z, 0 ≤ y w) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Real.sqrt (x w) * Real.sqrt (y w)
      ≤ Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, x w)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, y w) := by
  have hc : 0 ≤ (Z.card : ℝ)⁻¹ := by positivity
  have hsq : ∑ w ∈ Z, Real.sqrt (x w) * Real.sqrt (y w)
      ≤ Real.sqrt (∑ w ∈ Z, x w) * Real.sqrt (∑ w ∈ Z, y w) := by
    have h1 : ∑ w ∈ Z, Real.sqrt (x w) ^ 2 = ∑ w ∈ Z, x w :=
      Finset.sum_congr rfl fun w hw => Real.sq_sqrt (hx w hw)
    have h2 : ∑ w ∈ Z, Real.sqrt (y w) ^ 2 = ∑ w ∈ Z, y w :=
      Finset.sum_congr rfl fun w hw => Real.sq_sqrt (hy w hw)
    have h := Real.sum_mul_le_sqrt_mul_sqrt Z
      (fun w => Real.sqrt (x w)) (fun w => Real.sqrt (y w))
    simpa only [h1, h2] using h
  have hsqrt : Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, x w)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, y w)
      = (Z.card : ℝ)⁻¹
        * (Real.sqrt (∑ w ∈ Z, x w) * Real.sqrt (∑ w ∈ Z, y w)) := by
    rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
    conv_rhs => rw [← Real.mul_self_sqrt hc]
    ring
  calc
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Real.sqrt (x w) * Real.sqrt (y w)
        ≤ (Z.card : ℝ)⁻¹
          * (Real.sqrt (∑ w ∈ Z, x w) * Real.sqrt (∑ w ∈ Z, y w)) :=
          mul_le_mul_of_nonneg_left hsq hc
    _ = Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, x w)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, y w) := hsqrt.symm

end

end Homogenization.HighContrast.Multiscale
