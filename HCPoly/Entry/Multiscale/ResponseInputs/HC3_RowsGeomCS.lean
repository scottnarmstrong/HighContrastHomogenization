import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The descendant sum against the source-load weights

For the response transfer of `p.response.transfer`, the within-cell oscillation of the cutoff is
paired with the gradient and the flux at every descendant generation, the generation-`n` term
carrying the factor `3^{-H-n}`.  Summing the descendants against the source-load weights and
applying Cauchy--Schwarz across the generations splits `3^{-n} = 3^{-n/4} · 3^{-3n/4}` and bounds
the descendant sum by the square root of the load times the square root of a convergent geometric
series.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The geometric series `∑ n, 3^{-n/2}` converges: its terms are `(3^{-1/2})^n` and
`3^{-1/2} < 1`. -/
theorem summable_rpow_neg_half : Summable fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
  have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hnn : 0 ≤ (3 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  refine (summable_geometric_of_lt_one hnn hlt).congr fun n => ?_
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [show (-(1 : ℝ) / 2) * (n : ℝ) = -((n : ℝ) / 2) by ring]

/-- Cauchy--Schwarz across the descendant generations bounds the descendant sum
`∑ n, 3^{-n} √(L n)` by the square root of the source-load weighted sum `∑ n, 3^{-3n/2} L n`,
multiplied by the square root of the convergent geometric series `∑ n, 3^{-n/2}`.  Splitting
`3^{-n} = 3^{-n/4} · 3^{-3n/4}` is what keeps the printed factor `3^{-H}(E[J_t]𝓛_s)^{1/2}` of
`p.response.transfer`. -/
theorem tsum_weighted_sqrt_le_sqrt_mul_sqrt (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
    (hsum' : Summable fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :
    (∑' n : ℕ, (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n))
      ≤ Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) := by
  let u : ℕ → ℝ := fun n => (3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))
  let v : ℕ → ℝ := fun n => (3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n)
  have hu_sq : ∀ n, u n ^ 2 = (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
    intro n
    change ((3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))) ^ 2 = (3 : ℝ) ^ (-((n : ℝ) / 2))
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [show (-(1 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((n : ℝ) / 2) by ring]
  have hv_sq : ∀ n, v n ^ 2 = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
    intro n
    change ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n)) ^ 2
      = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n
    rw [← Real.rpow_natCast]
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [Real.rpow_natCast, Real.sq_sqrt (hL n)]
    rw [show (-(3 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℝ) / 2) * (n : ℝ) by ring]
  have huv : ∀ n, u n * v n = (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := by
    intro n
    change (3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))
        * ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n))
      = (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (-(1 : ℝ) / 4 * (n : ℝ)) + (-(3 : ℝ) / 4 * (n : ℝ)) = -(n : ℝ) by ring]
  have huv_fun : (fun n : ℕ => u n * v n)
      = fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := funext huv
  have hpartial : ∀ s : Finset ℕ, ∑ n ∈ s, u n * v n
      ≤ Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) := by
    intro s
    refine (Real.sum_mul_le_sqrt_mul_sqrt s u v).trans ?_
    have hu_fin : ∑ n ∈ s, u n ^ 2 ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
      calc ∑ n ∈ s, u n ^ 2 = ∑ n ∈ s, (3 : ℝ) ^ (-((n : ℝ) / 2)) :=
            Finset.sum_congr rfl fun n _ => hu_sq n
        _ ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) :=
            summable_rpow_neg_half.sum_le_tsum s fun _ _ =>
              Real.rpow_nonneg (by norm_num) _
    have hv_fin : ∑ n ∈ s, v n ^ 2
        ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
      calc ∑ n ∈ s, v n ^ 2
          = ∑ n ∈ s, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n :=
            Finset.sum_congr rfl fun n _ => hv_sq n
        _ ≤ ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n :=
            hsum.sum_le_tsum s fun _ _ =>
              mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hL _)
    exact mul_le_mul (Real.sqrt_le_sqrt hu_fin) (Real.sqrt_le_sqrt hv_fin)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum_uv : Summable fun n : ℕ => u n * v n := by
    rw [huv_fun]
    exact hsum'
  have hmain := hsum_uv.tsum_le_of_sum_le hpartial
  rw [huv_fun] at hmain
  exact hmain

end

end Homogenization.HighContrast.Multiscale
