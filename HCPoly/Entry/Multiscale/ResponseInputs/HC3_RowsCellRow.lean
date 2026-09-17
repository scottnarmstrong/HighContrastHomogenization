import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsProdCS

/-!
# The cell pairing row of the cutoff-mean estimate, abstractly

The cell half of the two cutoff-mean rows of `e.response.cutoff.estimate` pairs the cutoff
fluctuation cell averages `c w`, bounded by one in absolute value, against a full-dual pairing
`pairing w a`.  Each subcell contributes a pairing controlled pathwise by the cell's own
source-load head `G w a` times the square root of twice its scalar deficit `D w a`.  Averaging the
bounded weight against that pathwise control and then applying the discrete and the annealed
Cauchy--Schwarz inequalities bounds the modulus of the sample expectation by the geometric mean of
the annealed head and the annealed flat deficit, the latter being exactly `2 tau`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cell pairing row of the cutoff-mean estimate.**  Let `c` be the cutoff fluctuation cell
averages, bounded by one on the finite index set `Z`, and let `pairing` be a full-dual pairing whose
subcell values are controlled pathwise by the source-load head `G` and the scalar deficit `D`
through `|pairing w a| ≤ G w a * √(2 * D w a)`.  If the annealed flat average of `G ^ 2` is at most
`Lhead` and the annealed flat average of `2 * D` equals `2 * tau`, then the modulus of the sample
expectation of the weighted flat average of `c w * pairing w a` is at most `√Lhead * √(2 * tau)`.
This is the cell half of the two cutoff-mean rows of `e.response.cutoff.estimate`. -/
theorem abs_integral_flat_weighted_pairing_le {iota alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) (Z : Finset iota) (c : iota → ℝ) (hc : ∀ w ∈ Z, |c w| ≤ 1)
    (pairing G D : iota → alpha → ℝ) (Lhead tau : ℝ)
    (hG : ∀ w ∈ Z, ∀ a, 0 ≤ G w a) (hD : ∀ w ∈ Z, ∀ a, 0 ≤ D w a)
    (hbd : ∀ w ∈ Z, ∀ a, |pairing w a| ≤ G w a * Real.sqrt (2 * D w a))
    (hGsq : (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P) ≤ Lhead)
    (hDval : (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) = 2 * tau)
    (hFint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2) P)
    (hDint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) P)
    (hPint : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
      c w * (Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a))) P)
    (hPint' : Integrable (fun a => (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a) P) :
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a ∂P|
      ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) := by
  have hprod : |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        c w * (Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a)) ∂P|
      ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) := by
    have h0 := abs_integral_flat_weighted_prod_le P Z c hc
      (fun w a => (G w a) ^ 2) (fun w a => 2 * D w a)
      (fun w _ a => sq_nonneg (G w a))
      (fun w hw a => by linarith [hD w hw a])
      hFint hDint hMidint hPint
    calc
      |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
          c w * (Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a)) ∂P|
          ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) := h0
      _ = Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (2 * tau) := by rw [hDval]
      _ ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGsq) (Real.sqrt_nonneg _)
  have hpt : ∀ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a|
      ≤ Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) := by
    intro a
    have h1 := abs_flat_average_weighted_le Z c (fun w => pairing w a) hc
    have h2 : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |pairing w a|
        ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
            Real.sqrt ((G w a) ^ 2) * Real.sqrt (2 * D w a) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun w hw => by
          rw [Real.sqrt_sq (hG w hw a)]
          exact hbd w hw a)
        (by positivity)
    have h3 := flat_average_sqrt_mul_sqrt_le Z (fun w => (G w a) ^ 2)
      (fun w => 2 * D w a)
      (fun w _ => sq_nonneg (G w a))
      (fun w hw => by linarith [hD w hw a])
    exact h1.trans (h2.trans h3)
  have hF0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => sq_nonneg (G w a))
  have hD0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a := by
    intro a
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun w hw => by linarith [hD w hw a])
  calc
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a ∂P|
        ≤ ∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a| ∂P :=
          abs_integral_le_integral_abs
    _ ≤ ∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P :=
          integral_mono hPint'.abs hMidint hpt
    _ ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
          * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) :=
          integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hFint hDint hF0 hD0 hMidint
    _ = Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
          * Real.sqrt (2 * tau) := by rw [hDval]
    _ ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGsq) (Real.sqrt_nonneg _)

end

end Homogenization.HighContrast.Multiscale
