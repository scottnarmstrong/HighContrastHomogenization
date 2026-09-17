import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectMeanCancel
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRowArith

/-!
# The first error row in abstract bookkeeping form

The terminal-optimizer replacement of `p.response.transfer`, after the terminal cell is subdivided
into the aligned coarse cells, reduces to the following bookkeeping.  Each subcell carries three
sample functions: the response `J`, half the restricted terminal optimizer energy `E`, and the
nonnegative deficit `D` between them, compared pointwise by `|E - J| ≤ D + 2 √(J D)`.  The weights
`c` are the subcell means of the cutoff fluctuation and average to zero, stationarity makes the
annealed response `∫ J` the same `cJ` on every subcell, and the annealed flat average of the
deficits is the scale defect `τ`.

The weighted average of the half-energies then has expectation at most `τ + 2 √(τ cJ)`: the
`J`-part is annihilated by the mean-zero weights, and the remainder is controlled by the deficits
through the one-parameter Cauchy--Schwarz bound `2 √(J D) ≤ ε J + D / ε`.

Paper: `p.response.transfer`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The abstract first error row.**  Under the pointwise comparison `|E - J| ≤ D + 2 √(J D)`, a
common annealed response `∫ J w = cJ`, a mean-zero normalized weighting `c`, and an annealed
flat deficit `τ`, the expectation of the weighted average of the half-energies is at most
`τ + 2 √(τ cJ)`.  This is the bookkeeping content of the terminal-optimizer replacement of the
first error row of `p.response.transfer`. -/
theorem abs_integral_avsum_weighted_energy_le {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P] {d : ℕ} (n : ℕ)
    (c : (Fin d → ℤ) → ℝ) (E J D : (Fin d → ℤ) → α → ℝ) (cJ τ : ℝ)
    (hc0 : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d n, |c w| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ J w a)
    (hD0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ D w a)
    (hcmp : ∀ w ∈ triadicIndexBox d n, ∀ a,
      |E w a - J w a| ≤ D w a + 2 * Real.sqrt (J w a * D w a))
    (hJint : ∀ w ∈ triadicIndexBox d n, Integrable (J w) P)
    (hDint : ∀ w ∈ triadicIndexBox d n, Integrable (D w) P)
    (hEint : ∀ w ∈ triadicIndexBox d n, Integrable (E w) P)
    (hJval : ∀ w ∈ triadicIndexBox d n, (∫ a, J w a ∂P) = cJ)
    (hDval : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, D w a ∂P) = τ) :
    |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P|
      ≤ τ + 2 * Real.sqrt (τ * cJ) := by
  have hcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d :=
    card_triadicIndexBox n
  have hZcard_pos : (0 : ℝ) < ((triadicIndexBox d n).card : ℝ) := by
    rw [hcard]
    positivity
  have hNnonneg : 0 ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ :=
    inv_nonneg.mpr hZcard_pos.le
  have hNcard : (((triadicIndexBox d n).card : ℝ))⁻¹ * ((triadicIndexBox d n).card : ℝ) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hZcard_pos)
  have hFJint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * J w a) P :=
    (integrable_finsetSum _ (fun w hw => (hJint w hw).const_mul (c w))).const_mul _
  have hFEJint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)) P :=
    (integrable_finsetSum _
      (fun w hw => ((hEint w hw).sub (hJint w hw)).const_mul (c w))).const_mul _
  have hFEJabs : Integrable (fun a => |(((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)|) P := by
    simpa only [Real.norm_eq_abs] using hFEJint.abs
  have hFE_split : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)
      = (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * J w a ∂P)
        + (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) ∂P) := by
    have hpt : ∀ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * E w a
        = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * J w a
          + (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) := by
      intro a
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hFJint hFEJint]
  have hFJcancel : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * J w a ∂P) = 0 :=
    integral_avsum_mul_eq_zero P n c J cJ hc0 hJval hJint
  have hFE_eq : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)
      = (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) ∂P) := by
    rw [hFE_split, hFJcancel, zero_add]
  have hDsum : (∫ a, ∑ w ∈ triadicIndexBox d n, D w a ∂P)
      = ∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P) :=
    integral_finsetSum _ (fun w hw => hDint w hw)
  have hNStau : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P) = τ := by
    have key := hDval
    rw [integral_const_mul, hDsum] at key
    exact key
  have hmain : ∀ ε : ℝ, 0 < ε →
      |(∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)|
        ≤ τ + (ε * cJ + τ / ε) := by
    intro ε hε
    have hinner : ∀ w ∈ triadicIndexBox d n,
        (∫ a, (D w a + ε * J w a + D w a / ε) ∂P)
          = (∫ a, D w a ∂P) + ε * cJ + (∫ a, D w a ∂P) / ε := by
      intro w hw
      have hsplit : (∫ a, (D w a + ε * J w a + D w a / ε) ∂P)
          = (∫ a, (D w a + ε * J w a) ∂P) + (∫ a, D w a / ε ∂P) :=
        integral_add
          (show Integrable (fun a => D w a + ε * J w a) P from
            (hDint w hw).add ((hJint w hw).const_mul ε))
          ((hDint w hw).div_const ε)
      have hDJ : (∫ a, (D w a + ε * J w a) ∂P)
          = (∫ a, D w a ∂P) + (∫ a, ε * J w a ∂P) :=
        integral_add (hDint w hw) ((hJint w hw).const_mul ε)
      rw [hsplit, hDJ, integral_const_mul, hJval w hw,
        integral_div ε (fun a => D w a)]
    have hsum_eval : (∑ w ∈ triadicIndexBox d n,
          ((∫ a, D w a ∂P) + ε * cJ + (∫ a, D w a ∂P) / ε))
        = (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
          + (((triadicIndexBox d n).card : ℝ) * (ε * cJ))
          + (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P)) / ε := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_div]
    have hsum_congr : (∑ w ∈ triadicIndexBox d n,
          (∫ a, (D w a + ε * J w a + D w a / ε) ∂P))
        = ∑ w ∈ triadicIndexBox d n,
            ((∫ a, D w a ∂P) + ε * cJ + (∫ a, D w a ∂P) / ε) :=
      Finset.sum_congr rfl (fun w hw => hinner w hw)
    have hGε_int : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) ∂P)
        = τ + ε * cJ + τ / ε := by
      have hconst : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) ∂P)
          = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            (∫ a, ∑ w ∈ triadicIndexBox d n,
              (D w a + ε * J w a + D w a / ε) ∂P) :=
        integral_const_mul _ (fun a => ∑ w ∈ triadicIndexBox d n,
          (D w a + ε * J w a + D w a / ε))
      have hsum : (∫ a, ∑ w ∈ triadicIndexBox d n,
            (D w a + ε * J w a + D w a / ε) ∂P)
          = ∑ w ∈ triadicIndexBox d n,
            (∫ a, (D w a + ε * J w a + D w a / ε) ∂P) :=
        integral_finsetSum _ (fun w hw =>
          show Integrable (fun a => D w a + ε * J w a + D w a / ε) P from
            ((hDint w hw).add ((hJint w hw).const_mul ε)).add
              ((hDint w hw).div_const ε))
      rw [hconst, hsum, hsum_congr, hsum_eval]
      calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ((∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
              + (((triadicIndexBox d n).card : ℝ) * (ε * cJ))
              + (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P)) / ε)
          = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
            + (((triadicIndexBox d n).card : ℝ))⁻¹ *
              (((triadicIndexBox d n).card : ℝ) * (ε * cJ))
            + (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ((∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P)) / ε) := by ring
        _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
            + ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ((triadicIndexBox d n).card : ℝ)) * (ε * cJ)
            + ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))) / ε := by ring
        _ = τ + ε * cJ + τ / ε := by rw [hNStau, hNcard]; ring
    have hpt : ∀ a, |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)|
        ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) := by
      intro a
      calc |(((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)|
          = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              |∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)| := by
            rw [abs_mul, abs_of_nonneg hNnonneg]
        _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, |c w * (E w a - J w a)| :=
            mul_le_mul_of_nonneg_left
              (Finset.abs_sum_le_sum_abs
                (fun w => c w * (E w a - J w a)) (triadicIndexBox d n))
              hNnonneg
        _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, |c w| * |E w a - J w a| := by
            congr 1
            exact Finset.sum_congr rfl (fun w _ => by rw [abs_mul])
        _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, 1 * |E w a - J w a| := by
            apply mul_le_mul_of_nonneg_left _ hNnonneg
            apply Finset.sum_le_sum
            intro w hw
            exact mul_le_mul_of_nonneg_right (hc1 w hw) (abs_nonneg _)
        _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, |E w a - J w a| := by
            congr 1
            exact Finset.sum_congr rfl (fun w _ => by rw [one_mul])
        _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) := by
            apply mul_le_mul_of_nonneg_left _ hNnonneg
            apply Finset.sum_le_sum
            intro w hw
            calc |E w a - J w a|
                ≤ D w a + 2 * Real.sqrt (J w a * D w a) := hcmp w hw a
              _ ≤ D w a + (ε * J w a + D w a / ε) := by
                  have hY := two_mul_sqrt_mul_le_eps_add_div (J w a) (D w a) ε
                    (hJ0 w hw a) (hD0 w hw a) hε
                  linarith
              _ = D w a + ε * J w a + D w a / ε := by ring
    have hGεint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε)) P :=
      (integrable_finsetSum _ (fun w hw =>
        show Integrable (fun a => D w a + ε * J w a + D w a / ε) P from
          ((hDint w hw).add ((hJint w hw).const_mul ε)).add
            ((hDint w hw).div_const ε))).const_mul _
    calc |(∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)|
        = |(∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) ∂P)| := by rw [hFE_eq]
      _ ≤ ∫ a, |(((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) ∂P :=
          integral_mono hFEJabs hGεint (fun a => hpt a)
      _ = τ + ε * cJ + τ / ε := hGε_int
      _ = τ + (ε * cJ + τ / ε) := by ring
  have hcJ_nonneg : 0 ≤ cJ := by
    have hZnonempty : (triadicIndexBox d n).Nonempty :=
      Finset.card_pos.mp (Nat.cast_pos'.mp hZcard_pos)
    obtain ⟨w0, hw0⟩ := hZnonempty
    rw [← hJval w0 hw0]
    exact integral_nonneg (fun a => hJ0 w0 hw0 a)
  have hτ_nonneg : 0 ≤ τ := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg hNnonneg
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  exact le_add_two_mul_sqrt_of_forall_pos _ τ cJ τ hcJ_nonneg hτ_nonneg hmain

end

end Homogenization.HighContrast.Multiscale
