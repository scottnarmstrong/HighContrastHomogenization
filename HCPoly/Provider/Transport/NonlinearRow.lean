/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CellGap

/-!
# The nonlinear row of the transported budget

The transport keeps the complete nonlinear history: at every continued target
level `j < n` the gain of the new relative mean is charged to the gains of the
old ones, one bulk term at the shifted scale `j - λ_j` and a boundary row over
the scales below it.  This file closes that display,
`e.two.grid.whitney.mean.bound`.

The route is the printed one.  Monotonicity of the trace on the sandwich
`I ≤ P_{j,n}^{q'} ≤ K_W` gives `𝔥_Q(P_{j,n}^{q'}) ≤ 𝔥_Q(K_W)`, the lower half of
the comparison between the gap functional and the mean penalty turns the gain of
the upper mean into its gap functional, and `e.two.grid.whitney.mean.bound`
evaluates the latter as the weighted gain of the selected cells plus the bridge
error plus the two source terms.

What remains is the bookkeeping of the weights.  The selected cells of a target
cell are grouped by their scale; the weight of a scale is the total relative
volume of the cells of that scale, so the weights are nonnegative and of total
mass at most one, and the deficit is filled with the identity.  The deepest
scale `j - λ_j` is the bulk row and its weight is bounded by the total mass; the
scales below it form the boundary rows and their weights obey the conservative
bound `3^{-(1-g)(j-r)}`.  Substituting the two bounds into the weighted sum
produces exactly the printed row.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

section Blocks

variable {d : ℕ}

/-! ## The gain of a block below an upper mean -/

/-- The gain of a block above the identity is nonnegative. -/
theorem zero_le_frakH {Q : ℝ} (hQ : 0 ≤ Q) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) : 0 ≤ frakH Q Pm := by
  have hx := zero_le_trace_gap hPm
  have h1 : (1 : ℝ) ^ Q ≤ (1 + (blockTrace Pm - 2 * (d : ℝ))) ^ Q :=
    Real.rpow_le_rpow zero_le_one (by linarith only [hx]) hQ
  rw [Real.one_rpow] at h1
  rw [frakH]
  linarith only [h1]

/-- **The trace step of `e.two.grid.whitney.mean.bound`.**  A block caught
between the identity and an upper mean has gain at most a constant times the gap
functional of that mean: the trace is monotone, and the two gain functions are
comparable. -/
theorem frakH_le_gapG_of_le (hd : 0 < d) {Q : ℝ} (hQ : 1 ≤ Q) {H K : BlockMat d}
    (hIH : (1 : FullBlockMat d) ≤ toFullBlockMat H)
    (hHK : toFullBlockMat H ≤ toFullBlockMat K) : frakH Q H ≤ 2 ^ Q * gapG Q K := by
  have hstep := frakH_le_of_le (Q := Q) (by linarith only [hQ]) hIH hHK
  have hcomp := frakH_le_rpow_mul_gapG hd hQ (hIH.trans hHK)
  linarith only [hstep, hcomp]

/-! ## The printed row -/

/-- **`e.two.grid.whitney.mean.bound`.**  At a continued target level the
gain of the new relative mean is a constant times the gain of the old relative
mean at the shifted scale, plus the same constant times the boundary row of the
lower scales, plus the same constant times the bridge error and the two source
terms.

The selected cells are grouped by scale, `theta r` being the total relative
volume of the selected cells of scale `r`; the deepest scale carries the bulk
term and the scales below it obey the conservative row
`3^{-(1-g)(j-r)}`. -/
theorem nonlinear_row (hd : 1 ≤ d) {Q g : ℝ} (hQ : 1 ≤ Q) {jStar j lam : ℤ}
    (hlam : jStar ≤ j - lam) {theta : ℤ → ℝ} {Pold : ℤ → BlockMat d}
    {Pnew Pbar Mblk Phat KW Rm : BlockMat d} {S : FullBlockMat d} {eta eps Cb : ℝ}
    (hth : ∀ r ∈ Finset.Icc jStar (j - lam), 0 ≤ theta r)
    (hm : ∑ r ∈ Finset.Icc jStar (j - lam), theta r ≤ 1)
    (hbdry : ∀ r ∈ Finset.Ico jStar (j - lam),
      theta r ≤ Cb * (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))))
    (hPold : ∀ r ∈ Finset.Icc jStar (j - lam),
      (1 : FullBlockMat d) ≤ toFullBlockMat (Pold r))
    (hPbar : toFullBlockMat Pbar =
      ∑ r ∈ Finset.Icc jStar (j - lam), theta r • toFullBlockMat (Pold r) +
        (1 - ∑ r ∈ Finset.Icc jStar (j - lam), theta r) • (1 : FullBlockMat d))
    (heta : 0 ≤ eta) (heta3 : eta ≤ 1 / 3) (heps : 0 ≤ eps)
    (hS : Sᵀ * S ≤ (1 + eta) • (1 : FullBlockMat d))
    (hR : toFullBlockMat Rm ≤ eps • (1 : FullBlockMat d))
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk))
    (hKW : toFullBlockMat KW =
      Sᵀ * toFullBlockMat Pbar * S -
        (1 - ∑ r ∈ Finset.Icc jStar (j - lam), theta r) • (Sᵀ * S) + toFullBlockMat Rm)
    (hIP : (1 : FullBlockMat d) ≤ toFullBlockMat Pnew)
    (hPK : toFullBlockMat Pnew ≤ toFullBlockMat KW) :
    frakH Q Pnew ≤ 2 ^ (2 * Q + 1) * (1 + 2 * (d : ℝ)) ^ Q *
      (frakH Q (Pold (j - lam)) +
        Cb * ∑ r ∈ Finset.Ico jStar (j - lam),
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (Pold r) +
          3 * eta + (eps + eps ^ Q)) := by
  classical
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hE0 : (0 : ℝ) ≤ (2 : ℝ) ^ Q := Real.rpow_nonneg (by norm_num) _
  have hK0 : (0 : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ Q := Real.rpow_nonneg (by linarith only [hdR]) _
  have hIK : (1 : FullBlockMat d) ≤ toFullBlockMat KW := hIP.trans hPK
  -- the two printed steps
  have hfr := frakH_le_gapG_of_le (by omega : 0 < d) hQ hIP hPK
  have hcg := cell_gap (Finset.Icc jStar (j - lam)) hd hQ hth hm hPold hPbar heta heta3
    heps hS hR hM hPhat hKW hIK
  -- the weights, grouped by scale
  have hmem : (j - lam) ∈ Finset.Icc jStar (j - lam) := Finset.mem_Icc.mpr ⟨hlam, le_rfl⟩
  have hnotmem : (j - lam) ∉ Finset.Ico jStar (j - lam) := by
    simp only [Finset.mem_Ico, not_and, not_lt]
    exact fun _ => le_rfl
  have hins : insert (j - lam) (Finset.Ico jStar (j - lam)) = Finset.Icc jStar (j - lam) :=
    Finset.Ico_insert_right hlam
  have hsub : Finset.Ico jStar (j - lam) ⊆ Finset.Icc jStar (j - lam) := by
    rw [← hins]
    exact Finset.subset_insert _ _
  have hbulkw : theta (j - lam) ≤ 1 :=
    le_trans (Finset.single_le_sum (f := theta) hth hmem) hm
  have hgain0 : ∀ r ∈ Finset.Icc jStar (j - lam), 0 ≤ frakH Q (Pold r) := fun r hr =>
    zero_le_frakH hQ0 (hPold r hr)
  have hweights : ∑ r ∈ Finset.Icc jStar (j - lam), theta r * frakH Q (Pold r) ≤
      frakH Q (Pold (j - lam)) +
        Cb * ∑ r ∈ Finset.Ico jStar (j - lam),
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (Pold r) := by
    rw [← hins, Finset.sum_insert hnotmem]
    refine add_le_add ?_ ?_
    · have h := mul_le_mul_of_nonneg_right hbulkw (hgain0 _ hmem)
      linarith only [h]
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      have hg := hgain0 r (hsub hr)
      have h := mul_le_mul_of_nonneg_right (hbdry r hr) hg
      calc theta r * frakH Q (Pold r)
          ≤ Cb * (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (Pold r) := h
        _ = Cb * ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (Pold r)) := by ring
  -- assemble the two constants
  have hconst : (2 : ℝ) ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q) =
      2 ^ (2 * Q + 1) * (1 + 2 * (d : ℝ)) ^ Q := by
    rw [show 2 * Q + 1 = Q + (Q + 1) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  have hC00 : (0 : ℝ) ≤ 2 ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q) :=
    mul_nonneg hE0 (mul_nonneg (mul_nonneg (by norm_num) hE0) hK0)
  have hmono := mul_le_mul_of_nonneg_left hweights hC00
  have hstep := mul_le_mul_of_nonneg_left hcg hE0
  rw [← hconst]
  have hexpA : (2 : ℝ) ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q *
      ((∑ r ∈ Finset.Icc jStar (j - lam), theta r * frakH Q (Pold r)) + 3 * eta +
        (eps + eps ^ Q))) =
      2 ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q) *
          (∑ r ∈ Finset.Icc jStar (j - lam), theta r * frakH Q (Pold r)) +
        2 ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q) * (3 * eta + (eps + eps ^ Q)) := by ring
  have hexpB : (2 : ℝ) ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q) *
      (frakH Q (Pold (j - lam)) +
        Cb * ∑ r ∈ Finset.Ico jStar (j - lam),
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (Pold r) +
          3 * eta + (eps + eps ^ Q)) =
      2 ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q) *
          (frakH Q (Pold (j - lam)) +
            Cb * ∑ r ∈ Finset.Ico jStar (j - lam),
              (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (Pold r)) +
        2 ^ Q * (2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q) * (3 * eta + (eps + eps ^ Q)) := by ring
  linarith only [hfr, hstep, hmono, hexpA, hexpB]

end Blocks

end

end Transport
end HighContrast
end Homogenization
