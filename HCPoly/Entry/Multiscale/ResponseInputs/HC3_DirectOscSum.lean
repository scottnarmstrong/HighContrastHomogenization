import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCellRow
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsGeomCS

/-!
# The descendant sum of the cutoff-oscillation pairings

The second cutoff-mean row of `p.response.transfer` pairs the within-cell oscillations of the
cutoff with the gradient and the flux, and then sums the descendants with weights
`3^{3(k-s)/2}`.  At each descendant depth a finite family of cells carries a weight of size at
most a fixed multiple of `3^{-n}` and a pairing controlled pathwise by the source-load head `G`
times the square root of twice the scalar deficit `D`.  The depth-`n` row bounds the expectation
of the weighted flat average, and summing over the depths after splitting `3^{-n}` into a
geometric factor and a load factor turns the descendant sum into the printed factor
`3^{-H}(E[J_t]𝓛_s)^{1/2}`.

The first declaration is the depth row with the normalisation of the weight made explicit; the
second sums those rows over the depths.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cell pairing row against a weight bounded by `M`.**  The weighted flat average of a
full-dual pairing controlled pathwise by the source-load head `G` and the scalar deficit `D`,
against weights of size at most `M`, has sample expectation at most
`M · √Lhead · √(2 tau)`.  This is the cell pairing row of `p.response.transfer` with the
normalisation of the weight made explicit. -/
theorem abs_integral_flat_weighted_pairing_le_of_bound {iota alpha : Type*}
    [MeasurableSpace alpha] (P : Measure alpha) (Z : Finset iota) (c : iota → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ w ∈ Z, |c w| ≤ M)
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
      ≤ M * (Real.sqrt Lhead * Real.sqrt (2 * tau)) := by
  have _ := hPint
  have habs : ∀ v : iota → ℝ,
      |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * v w| ≤ M * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w|) := by
    intro v
    have hc0 : 0 ≤ (Z.card : ℝ)⁻¹ := by positivity
    have hS : |∑ w ∈ Z, c w * v w| ≤ M * ∑ w ∈ Z, |v w| := by
      calc
        |∑ w ∈ Z, c w * v w| ≤ ∑ w ∈ Z, |c w * v w| :=
          Finset.abs_sum_le_sum_abs (fun w => c w * v w) Z
        _ = ∑ w ∈ Z, |c w| * |v w| :=
          Finset.sum_congr rfl fun w _ => abs_mul (c w) (v w)
        _ ≤ ∑ w ∈ Z, M * |v w| :=
          Finset.sum_le_sum fun w hw =>
            mul_le_mul_of_nonneg_right (hc w hw) (abs_nonneg (v w))
        _ = M * ∑ w ∈ Z, |v w| := by rw [Finset.mul_sum]
    calc
      |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * v w|
          = (Z.card : ℝ)⁻¹ * |∑ w ∈ Z, c w * v w| := by
            rw [abs_mul, abs_of_nonneg hc0]
      _ ≤ (Z.card : ℝ)⁻¹ * (M * ∑ w ∈ Z, |v w|) :=
            mul_le_mul_of_nonneg_left hS hc0
      _ = M * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, |v w|) := by ring
  have hpt : ∀ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a|
      ≤ M * (Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) := by
    intro a
    have h1 := habs (fun w => pairing w a)
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
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hM).trans
      (mul_le_mul_of_nonneg_left h3 hM))
  have hF0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 := by
    intro a
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => sq_nonneg (G w a))
  have hD0 : ∀ a, 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a := by
    intro a
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun w hw => by linarith [hD w hw a])
  have hCS : (∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P)
      ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) := by
    calc
      (∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P)
          ≤ Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a ∂P) :=
            integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hFint hDint hF0 hD0 hMidint
      _ = Real.sqrt (∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2 ∂P)
            * Real.sqrt (2 * tau) := by rw [hDval]
      _ ≤ Real.sqrt Lhead * Real.sqrt (2 * tau) :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGsq) (Real.sqrt_nonneg _)
  have hInt : Integrable (fun a => M * (Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
        * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a))) P :=
    hMidint.const_mul M
  calc
    |∫ a, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a ∂P|
        ≤ ∫ a, |(Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w * pairing w a| ∂P :=
          abs_integral_le_integral_abs
    _ ≤ ∫ a, M * (Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a)) ∂P :=
          integral_mono hPint'.abs hInt hpt
    _ = M * (∫ a, Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (G w a) ^ 2)
          * Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, 2 * D w a) ∂P) := by
          rw [integral_const_mul]
    _ ≤ M * (Real.sqrt Lhead * Real.sqrt (2 * tau)) :=
          mul_le_mul_of_nonneg_left hCS hM

/-- **The descendant sum of the cutoff-oscillation pairings.**  At each depth `n` the weights
`θ n w` are of size at most `K · 3^{-n}`, the pairings are controlled pathwise by the head
`G n w a` and the deficit `D n w a`, the annealed flat average of `G²` is at most `L n` and the
annealed flat average of `2 D` is at most `2 EJ`.  Then every partial descendant sum is bounded
by `K · √(∑ 3^{-n/2}) · √(∑ 3^{-3n/2} L n) · √(2 EJ)`: this is the term
`3^{-H}(E[J_t]𝓛_s)^{1/2}` of `p.response.transfer`. -/
theorem abs_sum_range_descendant_pairing_le {iota alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) (Nn : ℕ) (Z : ℕ → Finset iota) (θ : ℕ → iota → ℝ)
    (pairing G D : ℕ → iota → alpha → ℝ) (L : ℕ → ℝ) (K EJ : ℝ)
    (hK : 0 ≤ K) (hEJ : 0 ≤ EJ) (hL : ∀ n, 0 ≤ L n)
    (hθ : ∀ n, ∀ w ∈ Z n, |θ n w| ≤ K * (3 : ℝ) ^ (-(n : ℝ)))
    (hG : ∀ n, ∀ w ∈ Z n, ∀ a, 0 ≤ G n w a)
    (hD : ∀ n, ∀ w ∈ Z n, ∀ a, 0 ≤ D n w a)
    (hbd : ∀ n, ∀ w ∈ Z n, ∀ a, |pairing n w a| ≤ G n w a * Real.sqrt (2 * D n w a))
    (hGsq : ∀ n, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, (G n w a) ^ 2 ∂P) ≤ L n)
    (hDval : ∀ n, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a ∂P) ≤ 2 * EJ)
    (hFint : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, (G n w a) ^ 2) P)
    (hDint : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a) P)
    (hMidint : ∀ n, Integrable (fun a =>
      Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, (G n w a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a)) P)
    (hPint : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n,
      θ n w * (Real.sqrt ((G n w a) ^ 2) * Real.sqrt (2 * D n w a))) P)
    (hPint' : ∀ n, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n,
      θ n w * pairing n w a) P)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
    (hsum' : Summable fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :
    |∑ n ∈ Finset.range Nn,
        ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
      ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
            * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n))
          * Real.sqrt (2 * EJ) := by
  have _ := hEJ
  have hdepth : ∀ n, |∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
      ≤ (K * Real.sqrt (2 * EJ)) * ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) := by
    intro n
    have hM : 0 ≤ K * (3 : ℝ) ^ (-(n : ℝ)) :=
      mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
    have h1 := abs_integral_flat_weighted_pairing_le_of_bound P (Z n) (θ n)
      (K * (3 : ℝ) ^ (-(n : ℝ))) hM (hθ n) (pairing n) (G n) (D n) (L n)
      ((1 / 2) * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a ∂P)
      (hG n) (hD n) (hbd n) (hGsq n) (by ring)
      (hFint n) (hDint n) (hMidint n) (hPint n) (hPint' n)
    have hle : 2 * ((1 / 2) * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a ∂P)
        ≤ 2 * EJ := by
      have h := hDval n
      linarith
    calc
      |∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
          ≤ (K * (3 : ℝ) ^ (-(n : ℝ)))
              * (Real.sqrt (L n)
                * Real.sqrt (2 * ((1 / 2) * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, 2 * D n w a ∂P))) :=
            h1
      _ ≤ (K * (3 : ℝ) ^ (-(n : ℝ))) * (Real.sqrt (L n) * Real.sqrt (2 * EJ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)) hM
      _ = (K * Real.sqrt (2 * EJ)) * ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) := by ring
  have hK2 : 0 ≤ K * Real.sqrt (2 * EJ) := mul_nonneg hK (Real.sqrt_nonneg _)
  have hterm : ∀ n : ℕ, 0 ≤ (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) :=
    fun n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  calc
    |∑ n ∈ Finset.range Nn,
        ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P|
        ≤ ∑ n ∈ Finset.range Nn,
            |∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P| :=
          Finset.abs_sum_le_sum_abs
            (fun n => ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ w ∈ Z n, θ n w * pairing n w a ∂P)
            (Finset.range Nn)
    _ ≤ ∑ n ∈ Finset.range Nn,
          (K * Real.sqrt (2 * EJ)) * ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :=
          Finset.sum_le_sum fun n _ => hdepth n
    _ = (K * Real.sqrt (2 * EJ)) *
          ∑ n ∈ Finset.range Nn, ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) := by
          rw [Finset.mul_sum]
    _ ≤ (K * Real.sqrt (2 * EJ)) *
          ∑' n : ℕ, ((3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :=
          mul_le_mul_of_nonneg_left
            (hsum'.sum_le_tsum (Finset.range Nn) fun n _ => hterm n) hK2
    _ ≤ (K * Real.sqrt (2 * EJ)) *
          (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
            * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)) :=
          mul_le_mul_of_nonneg_left
            (tsum_weighted_sqrt_le_sqrt_mul_sqrt L hL hsum hsum') hK2
    _ = K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
            * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n))
          * Real.sqrt (2 * EJ) := by ring

end

end Homogenization.HighContrast.Multiscale
