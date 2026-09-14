/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.TraceComparison
import HCPoly.Provider.PortableHistory.TraceGap
import HCPoly.Setup.Moments

/-!
# Reduction of shifted drift to terminal trace gaps

The weighted increment drift is first bounded by weighted gaps to its own
terminal mean.  A lower two-grid comparison then changes the inverse
normalization to the old-grid terminal mean with an explicit slack cost.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

private theorem sum_Icc_pred_eq_sum_Ico {f : ℤ → ℝ} {b n : ℤ} :
    ∑ r ∈ Finset.Icc (b + 1) n, f (r - 1) =
      ∑ j ∈ Finset.Ico b n, f j := by
  classical
  refine Finset.sum_bij (fun r _ => r - 1) ?_ ?_ ?_ ?_
  · intro r hr
    have hrange := Finset.mem_Icc.mp hr
    simp only [Finset.mem_Ico]
    omega
  · intro r _ s _ hrs
    omega
  · intro j hj
    refine ⟨j + 1, ?_, ?_⟩
    have hjrange := Finset.mem_Ico.mp hj
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro r _
    rfl

/-- A positive decreasing matrix row has weighted increments no larger than
the corresponding weighted gaps to its terminal matrix. -/
theorem weighted_increments_le_weighted_terminal_gaps
    {rho : ℝ} {b n : ℤ} (F : ℤ → FullBlockMat d)
    (hterminal : (F n).PosDef)
    (hterm : ∀ r ∈ Finset.Icc (b + 1) n, F n ≤ F r) :
    ∑ r ∈ Finset.Icc (b + 1) n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - (r : ℝ))) *
          Matrix.trace ((F n)⁻¹ * (F (r - 1) - F r)) ≤
      ∑ j ∈ Finset.Ico b n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          Matrix.trace ((F n)⁻¹ * (F j - F n)) := by
  have hrow : ∀ r ∈ Finset.Icc (b + 1) n,
      (3 : ℝ) ^ (-rho * ((n : ℝ) - (r : ℝ))) *
          Matrix.trace ((F n)⁻¹ * (F (r - 1) - F r)) ≤
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - ((r - 1 : ℤ) : ℝ))) *
          Matrix.trace ((F n)⁻¹ * (F (r - 1) - F n)) := by
    intro r hr
    have hdiff : F (r - 1) - F r ≤ F (r - 1) - F n :=
      sub_le_sub_left (hterm r hr) _
    have htrace := PortableHistory.trace_mul_le_trace_mul hterminal.inv.posSemidef hdiff
    have hweight :
        (3 : ℝ) ^ (-rho * ((n : ℝ) - (r : ℝ))) =
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - ((r - 1 : ℤ) : ℝ))) := by
      congr 1
      push_cast
      ring
    rw [hweight]
    exact mul_le_mul_of_nonneg_left htrace (Real.rpow_nonneg (by norm_num) _)
  refine (Finset.sum_le_sum hrow).trans_eq ?_
  change (∑ r ∈ Finset.Icc (b + 1) n,
      (fun j : ℤ => (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
        Matrix.trace ((F n)⁻¹ * (F j - F n))) (r - 1)) = _
  exact sum_Icc_pred_eq_sum_Ico
    (f := fun j : ℤ =>
      (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
        Matrix.trace ((F n)⁻¹ * (F j - F n))) (b := b) (n := n)

end

end Bridge
end HighContrast
end Homogenization
