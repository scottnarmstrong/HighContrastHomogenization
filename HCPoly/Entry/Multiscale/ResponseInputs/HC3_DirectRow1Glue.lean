import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Abstract

/-!
# The terminal-optimizer replacement row of `p.response.transfer`

The `(φ - 1)`-weighted optimizer energy on the terminal cell splits, over the subdivision into
the aligned cells of the coarse scale, into its oscillation part and its subcell-mean part.  The
oscillation part costs the Lipschitz gain of the cutoff class times the terminal response.  The
subcell-mean part is the mean-zero weighting of the subcell half-energies, and the abstract row
bounds its expectation by `τ + 2 √(τ cJ)`, where `τ` is the scale defect and `cJ` the common
annealed subcell response.  Since `cJ = EJ + τ` and `√(τ (EJ + τ)) ≤ √(τ EJ) + τ`, the two halves
combine into the printed shape `6 τ + 4 √(τ EJ) + 2 K EJ`.

Paper: `p.response.transfer`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal-optimizer replacement row.**  Suppose the terminal response `Wtot` differs from
the normalized mean-zero weighting `N ∑ c w Ecell w` of the subcell half-energies, where
`N = |triadicIndexBox d n|⁻¹`, by at most `K` times twice the terminal response `Jt`.  Suppose
further that on each subcell the half-energy `(1/2) Ecell` and the subcell response `J` satisfy the
one-parameter comparison `|(1/2) Ecell - J| ≤ D + 2 √(J D)` with nonnegative `J` and deficit `D`,
that the weights `c` are bounded by `1` and average to `0`, that `∫ J w = cJ` is the same on every
subcell, and that the annealed flat average of the deficits `D` is the scale defect `τ`.  When
`cJ = EJ + τ` with `EJ = ∫ Jt`, the expectation of the terminal response is at most
`6 τ + 4 √(τ EJ) + 2 K EJ`.  This is the first error row of `p.response.transfer` assembled from
its oscillation and subcell-mean halves. -/
theorem abs_integral_le_row1_of_parts {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {d : ℕ} (n : ℕ)
    (c : (Fin d → ℤ) → ℝ) (Ecell J D : (Fin d → ℤ) → α → ℝ) (Wtot Jt : α → ℝ)
    (K cJ τ EJ : ℝ) (hK : 0 ≤ K)
    (hosc : ∀ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ≤ K * (2 * Jt a))
    (hcmp : ∀ w ∈ triadicIndexBox d n, ∀ a,
      |(1 / 2 : ℝ) * Ecell w a - J w a| ≤ D w a + 2 * Real.sqrt (J w a * D w a))
    (hc0 : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d n, |c w| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ J w a)
    (hD0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ D w a)
    (hJt0 : ∀ a, 0 ≤ Jt a)
    (hJint : ∀ w ∈ triadicIndexBox d n, Integrable (J w) P)
    (hDint : ∀ w ∈ triadicIndexBox d n, Integrable (D w) P)
    (hEint : ∀ w ∈ triadicIndexBox d n, Integrable (Ecell w) P)
    (hWint : Integrable Wtot P) (hJtint : Integrable Jt P)
    (hJval : ∀ w ∈ triadicIndexBox d n, (∫ a, J w a ∂P) = cJ)
    (hDval : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, D w a ∂P) = τ)
    (hEJ : (∫ a, Jt a ∂P) = EJ) (hcJ : cJ = EJ + τ) :
    |∫ a, Wtot a ∂P| ≤ 6 * τ + 4 * Real.sqrt (τ * EJ) + 2 * K * EJ := by
  have hSint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) P :=
    (integrable_finsetSum _ (fun w hw => (hEint w hw).const_mul (c w))).const_mul _
  have hdiff_int : Integrable (fun a => Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) P := hWint.sub hSint
  have hdiff_abs_int : Integrable (fun a => |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a|) P := by
    simpa only [Real.norm_eq_abs] using hdiff_int.abs
  have hSplit : (∫ a, Wtot a ∂P)
      = (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P)
        + (∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P) := by
    rw [← integral_add hSint hdiff_int]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun a => by ring))
  have hAbsSplit : |∫ a, Wtot a ∂P|
      ≤ |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
        + |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P| := by
    rw [hSplit]
    exact abs_add_le _ _
  have hKabs : |K| = K := abs_of_nonneg hK
  have hoscK : ∀ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ≤ |K| * (2 * Jt a) := by
    intro a
    rw [hKabs]
    exact hosc a
  have hdiff_bound : |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P| ≤ 2 * K * EJ := by
    have hKJt_int : Integrable (fun a => |K| * (2 * Jt a)) P :=
      (hJtint.const_mul (2 : ℝ)).const_mul |K|
    have hmono : (∫ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ∂P)
        ≤ ∫ a, |K| * (2 * Jt a) ∂P :=
      integral_mono hdiff_abs_int hKJt_int hoscK
    have hKint : (∫ a, |K| * (2 * Jt a) ∂P) = 2 * K * EJ := by
      rw [integral_const_mul, integral_const_mul, hEJ, hKabs]
      ring
    calc |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P|
        ≤ ∫ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ a, |K| * (2 * Jt a) ∂P := hmono
      _ = 2 * K * EJ := hKint
  have hEint' : ∀ w ∈ triadicIndexBox d n,
      Integrable (fun a => (1 / 2 : ℝ) * Ecell w a) P :=
    fun w hw => (hEint w hw).const_mul (1 / 2 : ℝ)
  have habs : |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a) ∂P|
      ≤ τ + 2 * Real.sqrt (τ * cJ) :=
    abs_integral_avsum_weighted_energy_le P n c (fun w a => (1 / 2 : ℝ) * Ecell w a)
      J D cJ τ hc0 hc1 hJ0 hD0 hcmp hJint hDint hEint' hJval hDval
  have hS_eq : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P)
      = 2 * (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a) ∂P) := by
    have hpt : ∀ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a
        = 2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a)) := by
      intro a
      have hinner : (∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a))
          = (1 / 2 : ℝ) * ∑ w ∈ triadicIndexBox d n, c w * Ecell w a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      rw [hinner]
      ring
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hAbsS : |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
      ≤ 2 * (τ + 2 * Real.sqrt (τ * cJ)) := by
    rw [hS_eq, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact mul_le_mul_of_nonneg_left habs (show (0 : ℝ) ≤ 2 by norm_num)
  have hNnonneg : 0 ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ := by
    have hcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d :=
      card_triadicIndexBox n
    rw [hcard]
    positivity
  have hτ0 : 0 ≤ τ := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg hNnonneg
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  have hEJ0 : 0 ≤ EJ := by
    rw [← hEJ]
    exact integral_nonneg hJt0
  have hsqrt : Real.sqrt (τ * cJ) ≤ Real.sqrt (τ * EJ) + τ := by
    rw [hcJ]
    exact sqrt_mul_add_le_sqrt_mul_add EJ τ hEJ0 hτ0
  have hAbsS' : |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
      ≤ 2 * (τ + 2 * (Real.sqrt (τ * EJ) + τ)) := by
    have h2 : 2 * Real.sqrt (τ * cJ) ≤ 2 * (Real.sqrt (τ * EJ) + τ) :=
      mul_le_mul_of_nonneg_left hsqrt (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  calc |∫ a, Wtot a ∂P|
      ≤ |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
          + |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P| := hAbsSplit
    _ ≤ 2 * (τ + 2 * (Real.sqrt (τ * EJ) + τ)) + 2 * K * EJ :=
        add_le_add hAbsS' hdiff_bound
    _ = 6 * τ + 4 * Real.sqrt (τ * EJ) + 2 * K * EJ := by ring

end

end Homogenization.HighContrast.Multiscale
