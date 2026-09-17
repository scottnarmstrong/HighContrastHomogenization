import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsFlatWeight
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCSIntegral

/-!
# Cauchy--Schwarz with the expectation outside the cell average

The first error row of `e.response.cutoff.estimate` pairs the cutoff fluctuation cell averages
`c w`, which are bounded by one in absolute value, against the pathwise product `√(f w a) √(g w a)`
of the difference and cell energies.  The weighted flat average over the scale-`s` subcells is
controlled pathwise by the flat Cauchy--Schwarz product of the two energies, and the sample
expectation is then moved inside each factor by the annealed square-root Cauchy--Schwarz
inequality.  The result is the direct full-dual pairing estimate of `e.response.cutoff.estimate`:
the weights stay inside the cell average, while the expectation acts linearly on each energy.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Expectation outside the weighted cell average.**  Let `c` be the cutoff fluctuation cell
averages, bounded by one on the finite index set `Z`, and let `f` and `g` be nonnegative families of
sample functions.  Then the modulus of the sample expectation of the weighted flat average of
`c w * (√(f w a) * √(g w a))` is bounded by the product of the square roots of the sample
expectations of the flat averages of `f` and of `g`.

Pathwise, the bounded weights are peeled off by the flat weighted-average bound, and the remaining
flat average of `√(f w a) √(g w a)` is estimated by the discrete Cauchy--Schwarz inequality for
flat averages.  Integrating the resulting pointwise bound and applying the annealed square-root
Cauchy--Schwarz inequality moves the expectation inside each factor.  This is the weighted cell
step of `e.response.cutoff.estimate`. -/
theorem abs_integral_flat_weighted_prod_le {iota alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) (Z : Finset iota) (c : iota → ℝ) (hc : ∀ w ∈ Z, |c w| ≤ 1)
    (f g : iota → alpha → ℝ)
    (hf : ∀ w ∈ Z, ∀ a, 0 ≤ f w a) (hg : ∀ w ∈ Z, ∀ a, 0 ≤ g w a)
    (hFint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a) P)
    (hGint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a)) P)
    (hPint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
      c w * (Real.sqrt (f w a) * Real.sqrt (g w a))) P) :
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * (Real.sqrt (f w a) * Real.sqrt (g w a)) ∂P|
      ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a ∂P)
        * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a ∂P) := by
  have hpt : ∀ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt (f w a) * Real.sqrt (g w a))|
      ≤ Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) := by
    intro a
    have h1 := abs_flat_average_weighted_le Z c
      (fun w => Real.sqrt (f w a) * Real.sqrt (g w a)) hc
    have h2 : (Z.card : ℝ)⁻¹
          * ∑ w ∈ Z, |Real.sqrt (f w a) * Real.sqrt (g w a)|
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Real.sqrt (f w a) * Real.sqrt (g w a) := by
      congr 1
      exact Finset.sum_congr rfl fun w _ =>
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h3 := flat_average_sqrt_mul_sqrt_le Z (fun w => f w a) (fun w => g w a)
      (fun w hw => hf w hw a) (fun w hw => hg w hw a)
    exact h1.trans (h2.trans_le h3)
  have hF0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w hw => hf w hw a)
  have hG0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w hw => hg w hw a)
  have hmono : (∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt (f w a) * Real.sqrt (g w a))| ∂P)
      ≤ ∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) ∂P :=
    integral_mono hPint.abs hMidint hpt
  calc
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt (f w a) * Real.sqrt (g w a)) ∂P|
        ≤ ∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
            c w * (Real.sqrt (f w a) * Real.sqrt (g w a))| ∂P :=
          abs_integral_le_integral_abs
    _ ≤ ∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a) ∂P := hmono
    _ ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, f w a ∂P)
          * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, g w a ∂P) :=
          integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hFint hGint hF0 hG0 hMidint

end

end Homogenization.HighContrast.Multiscale
