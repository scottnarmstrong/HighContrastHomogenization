import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakBadBranchWeight

/-!
# The tail weight of the cell-average estimate, both branches at once

The cell-average estimate `e.response.weak.estimate` prints its older-scale tail weight as a
single `if` at the cutoff `1`: the branch `1 < M` contributes the recent-scale value `√M`, and its
complement the older-scale weight `3^{-(respAlpha γ * H)}`.  The two branches are discharged by
different lemmas elsewhere in the development; this file packages the case split once and for all,
so that a consumer carrying `M` need not first decide which branch it lies on.
-/

namespace Homogenization.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- On either branch of the cutoff `1 < M`, the smaller of `Real.sqrt M` and `θ` is at most the
branch value the cell-average estimate prints. -/
theorem h6a_le_tail_branch (M θ : ℝ) (_hM : 0 ≤ M) (_hθ : 0 ≤ θ) :
    min (Real.sqrt M) θ ≤ (if 1 < M then Real.sqrt M else θ) := by
  by_cases h : 1 < M
  · simp only [if_pos h]
    exact min_le_left _ _
  · simp only [if_neg h]
    exact min_le_right _ _

/-- The branch-free tail comparison behind `e.response.weak.estimate`: a value `Agood` bounded by
`cgood` times the older-scale weight on `M ≤ 1`, and a value `Abad` bounded by `cbad` times `√M`
on `1 < M`, are together dominated by `max cgood cbad` times the printed `if` tail weight. -/
theorem h6a_branchfree_tail_le (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (H : ℕ) (M : ℝ)
    (_hM : 0 ≤ M) (cgood cbad : ℝ) (_hcgood : 0 ≤ cgood) (_hcbad : 0 ≤ cbad)
    (Agood Abad : ℝ)
    (hgood : M ≤ 1 → Agood ≤ cgood * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))))
    (hbad : 1 < M → Abad ≤ cbad * Real.sqrt M) :
    (if 1 < M then Abad else Agood)
      ≤ max cgood cbad * (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) := by
  by_cases h : 1 < M
  · simp only [if_pos h]
    calc Abad ≤ cbad * Real.sqrt M := hbad h
      _ ≤ max cgood cbad * Real.sqrt M :=
          mul_le_mul_of_nonneg_right (le_max_right cgood cbad) (Real.sqrt_nonneg M)
  · simp only [if_neg h]
    have hr : 0 ≤ (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    calc Agood ≤ cgood * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) := hgood (not_lt.mp h)
      _ ≤ max cgood cbad * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left cgood cbad) hr

end

end Homogenization.HighContrast.Multiscale
