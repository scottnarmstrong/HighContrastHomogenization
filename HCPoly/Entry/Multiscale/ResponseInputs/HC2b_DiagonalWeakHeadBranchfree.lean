import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakTailBranch

/-!
# The branch-free head bound of the cell-average estimate

The cell-average estimate `e.response.weak.estimate` controls its finite-window head by a tail
term whose weight changes across the cutoff `1` of the all-scale maximum `M`: on `M ≤ 1` the head
is bounded through the older-scale weight `3 ^ (-(respAlpha γ * H))`, while on `1 < M` the whole
head is absorbed by the recent-scale weight `√M` alone.  This module assembles the two branch
bounds into a single estimate whose right-hand side carries the printed selector
`if 1 < M then √M else 3 ^ (-(respAlpha γ * H))`, so that a consumer carrying `M` need not decide
which side of the cutoff it lies on.

Both branch bounds enter as hypotheses and the head, the finite sums, the tail factor and the two
branch constants are abstract, so nothing here depends on how either branch is proved.
-/

namespace Homogenization.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The branch-free head bound behind `e.response.weak.estimate`.  If the head is bounded by
`Sums + cgood * 3 ^ (-(respAlpha γ * H)) * Tail` on `M ≤ 1` and by `cbad * √M * Tail` on `1 < M`,
with `Sums`, `Tail` and the two constants nonnegative, then it is bounded by `Sums` plus
`max cgood cbad` times the printed selector `if 1 < M then √M else 3 ^ (-(respAlpha γ * H))` times
`Tail`.  The good-branch weight is `3 ^ (-(respAlpha γ * H))` rather than `1`, and must occur with
that factor in the `M ≤ 1` hypothesis for the bound to hold. -/
theorem h6a_head_branchfree {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (H : ℕ) {M : ℝ}
    (hM0 : 0 ≤ M) (Head Sums Tail cgood cbad : ℝ)
    (hcgood : 0 ≤ cgood) (hcbad : 0 ≤ cbad) (hSums : 0 ≤ Sums) (hTail : 0 ≤ Tail)
    (hgood : M ≤ 1 → Head ≤ Sums + cgood * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) * Tail)
    (hbad : 1 < M → Head ≤ cbad * Real.sqrt M * Tail) :
    Head ≤ Sums + max cgood cbad *
      (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) * Tail := by
  have hw0 : 0 ≤ (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hcgood' : 0 ≤ cgood * Tail := mul_nonneg hcgood hTail
  have hcbad' : 0 ≤ cbad * Tail := mul_nonneg hcbad hTail
  have hgood' : M ≤ 1 → Head - Sums
      ≤ (cgood * Tail) * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) := by
    intro hMle
    calc Head - Sums ≤ cgood * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) * Tail := by
          linarith only [hgood hMle]
      _ = (cgood * Tail) * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) := by ring
  have hbad' : 1 < M → Head - Sums ≤ (cbad * Tail) * Real.sqrt M := by
    intro hMgt
    calc Head - Sums ≤ Head := by linarith only [hSums]
      _ ≤ cbad * Real.sqrt M * Tail := hbad hMgt
      _ = (cbad * Tail) * Real.sqrt M := by ring
  have hkey := h6a_branchfree_tail_le γ hγ H M hM0 (cgood * Tail) (cbad * Tail) hcgood' hcbad'
    (Head - Sums) (Head - Sums) hgood' hbad'
  have hkey' : Head - Sums ≤ max (cgood * Tail) (cbad * Tail) *
      (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) := by
    simpa only [ite_self] using hkey
  have hW0 : 0 ≤ (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) := by
    have hmin0 : 0 ≤ min (Real.sqrt M) ((3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) :=
      le_min (Real.sqrt_nonneg M) hw0
    exact le_trans hmin0 (h6a_le_tail_branch M ((3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) hM0 hw0)
  have hmax : max (cgood * Tail) (cbad * Tail) ≤ max cgood cbad * Tail := by
    refine max_le ?_ ?_
    · exact mul_le_mul_of_nonneg_right (le_max_left cgood cbad) hTail
    · exact mul_le_mul_of_nonneg_right (le_max_right cgood cbad) hTail
  have hstep : Head - Sums ≤ (max cgood cbad * Tail) *
      (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) :=
    le_trans hkey' (mul_le_mul_of_nonneg_right hmax hW0)
  calc Head = Sums + (Head - Sums) := by ring
    _ ≤ Sums + (max cgood cbad * Tail) *
          (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) := by
        linarith only [hstep]
    _ = Sums + max cgood cbad *
          (if 1 < M then Real.sqrt M else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) * Tail := by ring

end

end Homogenization.HighContrast.Multiscale
