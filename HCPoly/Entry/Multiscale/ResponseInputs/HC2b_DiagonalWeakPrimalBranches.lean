import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSeminormSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakTailSum

/-!
# The two branch bounds for the whole normalized scale-average seminorm

The cell-average estimate's left-hand side is the normalized seminorm
`3 ^ (-(t / 2)) * besovSeminorm t avg`, i.e. `∑' n, 3 ^ (-(n / 2)) * S n` with `S` the depth-`n`
scale average.  Given the per-scale bound `S n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · En`, the
printed estimate is proved in two branches.  On `1 < M` the whole series is absorbed by the
older-scale term; on `M ≤ 1` only the scales beyond the window `H` are, and the first `H + 1`
scales remain as an explicit head sum.  Nothing here mentions a matrix or a measure: both
statements are real analysis about the family `avg` alone.

The normalization `3 ^ (-(t / 2)) * besovSeminorm t avg = ∑' n, 3 ^ (-(n / 2)) * S n` is the
unsplit form of `h6a_normalized_besovTerm`; it is proved inline because the module that once
packaged it is not present, so the bad branch never needs the window split.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

variable {d : ℕ}

/-- The two branch bounds of the cell-average estimate for the whole normalized seminorm.  The
per-scale input is `S n ≤ √2 · K · (1 + √M · 3 ^ (respRho γ * n / 2)) · En`; summing it
geometrically gives the bad-branch bound `16 / (1 - respRho γ) · K · √M · En` on `1 < M`, and the
good-branch bound `∑_{n ≤ H} 3 ^ (-(n / 2)) S n + 16 / (1 - respRho γ) · K ·
3 ^ (-(respAlpha γ * H)) · En` on `M ≤ 1`. -/
theorem h6a_primal_branches {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (t : ℤ) (H : ℕ)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d) {K En M : ℝ}
    (hK : 0 ≤ K) (hEn : 0 ≤ En) (hM : 0 ≤ M)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
    (hscale : ∀ n : ℕ,
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))
        ≤ Real.sqrt 2 * K *
            (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) * En) :
    (1 < M → (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
        ≤ 16 / (1 - respRho γ) * K * Real.sqrt M * En) ∧
    (M ≤ 1 → (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
        ≤ (∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) *
              Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
                ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
          + 16 / (1 - respRho γ) * K * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) * En) := by
  constructor
  · intro hbad
    -- The bad branch works on the whole series, normalized termwise.
    have hnorm : (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
        = ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := by
      change (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          (∑' n : ℕ, (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
        = ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))
      rw [← tsum_mul_left]
      exact tsum_congr fun n => h6a_normalized_besovTerm t avg n
    rw [hnorm]
    exact h6a_tail_bad_le hγ hK hEn hbad
      (fun n : ℕ => Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
      (fun n => Real.sqrt_nonneg _) hscale
  · intro hgood
    -- The good branch keeps the head and bounds only the older scales beyond `H`.
    have hsplit := h6a_besovSeminorm_window_tail_eq t avg hsum H
    have htail := h6a_tail_good_le hγ H hK hEn hM hgood
      (fun n : ℕ => Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
      (fun n => Real.sqrt_nonneg _) hscale
    -- The split indexes the tail by `j + (H + 1)`, the good bound by `H + 1 + j`.
    have htail_eq : (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
          Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d (j + (H + 1)),
              blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)))
        = ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
          Real.sqrt ((((triadicIndexBox d (H + 1 + j)).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d (H + 1 + j),
              blockVecDot (avg (H + 1 + j) w) (avg (H + 1 + j) w)) := by
      apply tsum_congr
      intro j
      rw [Nat.add_comm j (H + 1)]
    rw [hsplit, htail_eq]
    exact add_le_add le_rfl htail

end

end Homogenization.HighContrast.Multiscale
