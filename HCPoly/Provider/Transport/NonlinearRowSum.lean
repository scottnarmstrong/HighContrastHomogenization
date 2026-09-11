/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.DiscreteConvolution

/-!
# Summing the nonlinear rows against the target weights

The nonlinear history of the new grid weights the row of each target level by
`w_n(j) = 3^{-a(n-1-j)}` and sums over the levels.  This file performs that sum
on the printed rows, entirely at the level of real sequences: the weighted total
of the rows is controlled by the weighted total of the old gains at the old
terminal scale, plus the bridge error, plus the weighted source rows.

The target levels come in the two regimes of
`e.two.grid.whitney.fine.bound`.  The first `ℓ₀` levels, `j_* ≤ j < j_*+ℓ₀`,
are early: there the whole target cell is treated as one source residual, so its
row is the source term alone, with neither a bulk nor a boundary contribution.
The continued levels `j_*+ℓ₀ ≤ j < n` are the ones the printed row
`e.two.grid.whitney.mean.bound` governs, and only those enter the two
convolutions.  The two regimes recombine in the source total, which runs over
every target level.

The gating of the continued levels is what makes the shifted scale admissible.
The adaptive depth of the Whitney filling lies between one and the buffer, so
`j ≥ j_*+ℓ₀` already forces the shifted scale `j-λ_j` into
the old window `[j_*, t)`; no separate depth hypothesis is needed, and none can
be imposed on the early levels, where `j-λ_j` falls below `j_*`.

Three mechanisms are at work on the continued levels, and all three are the
transport's own convolutions.  The bulk term shifts the source scale by the
auxiliary depth, and `e.two.grid.bulk.mean` converts the new
row weight into the old one at the cost `3^{2aℓ₀}`; the auxiliary depth takes
only two values, so at most two target scales are carried to a given source
scale and the shifted sum costs a further factor two.  The boundary terms are
summed by exchanging the two scales and applying
`e.two.grid.boundary.mean` at each source scale, which costs
one buffer factor and the geometric series of ratio `3^{-(1-g-a)}`; that series
converges exactly because `a < 1 - g`.  The bridge error acquires no buffer
factor at all: its weight is the row weight itself, and positivity of `a`
already sums it.

Only the truncation of the old gains needs care.  The multiplicity bound is
stated for a family that is nonnegative at every scale, while the gains are
nonnegative only on the window; the sum is therefore run on the family extended
by zero outside the window, which agrees with the gains where it matters because
every shifted scale stays inside.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

/-! ## Exchanging a target scale with its row of source scales -/

/-- A double sum over target scales and their rows of source scales, read as a
double sum over source scales and the target scales whose row contains them. -/
private theorem sum_boundary_comm {f : ℤ → ℤ → ℝ} {s T : Finset ℤ} {v : ℤ → Finset ℤ}
    (hv : ∀ j ∈ s, v j ⊆ T) :
    ∑ j ∈ s, ∑ r ∈ v j, f j r =
      ∑ r ∈ T, ∑ j ∈ s.filter fun j => r ∈ v j, f j r := by
  classical
  have hleft : ∀ j ∈ s, ∑ r ∈ v j, f j r = ∑ r ∈ T, if r ∈ v j then f j r else 0 := by
    intro j hj
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hv j hj)]
  rw [Finset.sum_congr rfl hleft, Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm

/-! ## The weighted total of the rows -/

/-- **The nonlinear rows, summed against the target weights.**  Each continued
target level obeys the printed row and each early level obeys the whole-source
row of `e.two.grid.whitney.fine.bound`; multiplying by the new row weight and
summing over all the levels converts the bulk term and the boundary terms into
the old row weights, at the cost of the two buffer factors, and leaves the
bridge error and the source rows as they stand.

The three coefficients on the right are the exact costs: `2` for the
two-to-one multiplicity of the auxiliary depth, the geometric constant
`3^{-(1-g-a)}/(1 - 3^{-(1-g-a)})` for the boundary series, and
`(1 - 3^{-a})^{-1}` for the total weight of a nonlinear row.  The early levels
are charged to the source coefficient alone, and their source rows join the
continued ones in the single source total on the right. -/
theorem nonlinear_rows_le {a g : ℝ} (ha : 0 < a) (hahi : a < 1 - g)
    {jStar n t l0 : ℤ} (ht : t = n + l0) (hl0 : 1 ≤ l0) {lam : ℤ → ℤ}
    (hlam : ∀ j, lam j = 1 ∨ lam j = l0)
    {C1 C2 C3 C4 etaX : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (heta : 0 ≤ etaX) {hold hnew src : ℤ → ℝ}
    (hold0 : ∀ r ∈ Finset.Ico jStar t, 0 ≤ hold r)
    (hearly : ∀ j ∈ Finset.Ico jStar (jStar + l0), hnew j ≤ C4 * src j)
    (hrow : ∀ j ∈ Finset.Ico (jStar + l0) n, hnew j ≤
      C1 * hold (j - lam j) +
        C2 * ∑ r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r +
        C3 * etaX + C4 * src j) :
    ∑ j ∈ Finset.Ico jStar n, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j ≤
      (2 * C1 + C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
          (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
          (∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m) +
        C3 / (1 - (3 : ℝ) ^ (-a)) * etaX +
        C4 * ∑ j ∈ Finset.Ico jStar n, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have htR : (t : ℝ) = (n : ℝ) + (l0 : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
  have hc : 0 < 1 - g - a := by linarith only [hahi]
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 - g - a)) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num)
      (neg_neg_iff_pos.mpr hc)
    linarith only [hlt]
  have hkappa : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))) :=
    div_nonneg (Real.rpow_nonneg h3.le _) hden.le
  have hbuf : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * a * (l0 : ℝ)) := Real.rpow_nonneg h3.le _
  have hbufle : (3 : ℝ) ^ (a * (l0 : ℝ)) ≤ (3 : ℝ) ^ (2 * a * (l0 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hl0R : (0 : ℝ) ≤ (l0 : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ l0)
    have hprod : (0 : ℝ) ≤ a * (l0 : ℝ) := mul_nonneg ha.le hl0R
    linarith only [hprod]
  have hwn : ∀ j : ℤ, (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) := fun _ =>
    Real.rpow_nonneg h3.le _
  -- the shifted scale of a continued level lies in the old window
  have hdepth : ∀ j ∈ Finset.Ico (jStar + l0) n,
      jStar ≤ j - lam j ∧ j - lam j < t := by
    intro j hj
    have hmem := Finset.mem_Ico.mp hj
    have hd := one_le_depth_and_le hl0 hlam j
    omega
  have hmemIco : ∀ j ∈ Finset.Ico (jStar + l0) n,
      j - lam j ∈ Finset.Ico jStar t := fun j hj => Finset.mem_Ico.mpr (hdepth j hj)
  have hsubIco : ∀ j ∈ Finset.Ico (jStar + l0) n,
      Finset.Ico jStar (j - lam j) ⊆ Finset.Ico jStar t := fun j hj =>
    Finset.Ico_subset_Ico le_rfl (le_of_lt (hdepth j hj).2)
  -- the continued levels inside the target range, and the early band left over
  have hsubK : Finset.Ico (jStar + l0) n ⊆ Finset.Ico jStar n :=
    Finset.Ico_subset_Ico (by omega) le_rfl
  have hsubE : Finset.Ico jStar n \ Finset.Ico (jStar + l0) n ⊆
      Finset.Ico jStar (jStar + l0) := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_Ico] at hj
    exact Finset.mem_Ico.mpr (by omega)
  -- the old rows, extended by zero outside the window
  set F : ℤ → ℝ := fun m => if m ∈ Finset.Ico jStar t then
    (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m else 0 with hFdef
  have hF0 : ∀ m, 0 ≤ F m := by
    intro m
    rw [hFdef]
    dsimp only
    by_cases hm : m ∈ Finset.Ico jStar t
    · rw [if_pos hm]
      exact mul_nonneg (Real.rpow_nonneg h3.le _) (hold0 m hm)
    · rw [if_neg hm]
  have hFval : ∀ m ∈ Finset.Ico jStar t,
      F m = (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m := by
    intro m hm
    rw [hFdef]
    dsimp only
    rw [if_pos hm]
  have hFsum : ∑ m ∈ Finset.Ico jStar t, F m =
      ∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m :=
    Finset.sum_congr rfl hFval
  clear_value F
  -- the bulk convolution
  have hbulk : ∑ j ∈ Finset.Ico (jStar + l0) n,
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hold (j - lam j) ≤
      2 * (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
        ∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m := by
    have hterm : ∀ j ∈ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hold (j - lam j) ≤
          (3 : ℝ) ^ (2 * a * (l0 : ℝ)) * F (j - lam j) := by
      intro j hj
      have hmem := hmemIco j hj
      have hconv := bulk_convolution_le (a := a) ha.le (l0 := (l0 : ℝ))
        (lam := ((lam j : ℤ) : ℝ)) (n := (n : ℝ)) (t := (t : ℝ)) (j := (j : ℝ)) htR
        (by exact_mod_cast (one_le_depth_and_le hl0 hlam j).2)
      have hcast : -a * ((t : ℝ) - 1 - ((j : ℝ) - ((lam j : ℤ) : ℝ))) =
          -a * ((t : ℝ) - 1 - (((j - lam j : ℤ)) : ℝ)) := by
        push_cast
        ring
      rw [hcast] at hconv
      rw [hFval _ hmem, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hconv (hold0 _ hmem)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, ← hFsum]
    have hmul := mul_le_mul_of_nonneg_left
      (sum_comp_sub_depth_le lam hlam (Finset.Ico (jStar + l0) n) (Finset.Ico jStar t)
        F hF0 hmemIco) hbuf
    linarith only [hmul]
  -- the boundary convolution
  have hbdry : ∑ j ∈ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
        ∑ r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r ≤
      (3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))) *
        (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
        ∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m := by
    have hswap : ∑ j ∈ Finset.Ico (jStar + l0) n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
          ∑ r ∈ Finset.Ico jStar (j - lam j),
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r =
        ∑ r ∈ Finset.Ico jStar t,
          ∑ j ∈ (Finset.Ico (jStar + l0) n).filter
            fun j => r ∈ Finset.Ico jStar (j - lam j),
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
              ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r) := by
      rw [← sum_boundary_comm
        (f := fun j r => (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
          ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r)) hsubIco]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    rw [hswap, Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrow0 := hold0 r hr
    have hs : ∀ j ∈ (Finset.Ico (jStar + l0) n).filter
        fun j => r ∈ Finset.Ico jStar (j - lam j), r + 1 ≤ j := by
      intro j hj
      obtain ⟨-, hj2⟩ := Finset.mem_filter.mp hj
      have hlt := (Finset.mem_Ico.mp hj2).2
      have hone := (one_le_depth_and_le hl0 hlam j).1
      omega
    have hconv := boundary_convolution (a := a) (g := g) hahi (l0 := l0) (n := n) (t := t)
      ht 1 r _ hs
    have hcast : -(1 - g - a) * (((1 : ℤ)) : ℝ) = -(1 - g - a) := by
      push_cast
      ring
    rw [hcast] at hconv
    have hfac : ∑ j ∈ (Finset.Ico (jStar + l0) n).filter
          fun j => r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r) =
        (∑ j ∈ (Finset.Ico (jStar + l0) n).filter
          fun j => r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ)))) * hold r := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfac]
    have hmul := mul_le_mul_of_nonneg_right hconv hrow0
    have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))) *
        ((3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r) :=
      mul_nonneg hkappa (mul_nonneg (Real.rpow_nonneg h3.le _) hrow0)
    have hshift := mul_le_mul_of_nonneg_right hbufle hnn
    linarith only [hmul, hshift]
  -- the bridge error, paid on the continued levels only
  have hbridge : ∑ j ∈ Finset.Ico (jStar + l0) n,
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * etaX ≤
      1 / (1 - (3 : ℝ) ^ (-a)) * etaX :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubK
      fun j _ _ => mul_nonneg (hwn j) heta) (bridge_error_nonlinear ha heta jStar n)
  -- the weighted rows of the continued levels
  have hterms : ∀ j ∈ Finset.Ico (jStar + l0) n,
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j ≤
        C1 * ((3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hold (j - lam j)) +
          C2 * ((3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            ∑ r ∈ Finset.Ico jStar (j - lam j),
              (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r) +
          C3 * ((3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * etaX) +
          C4 * ((3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j) := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hrow j hj) (hwn j)
    linarith only [h]
  have hsum := Finset.sum_le_sum hterms
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- the four contributions of the continued levels
  have hb1 := mul_le_mul_of_nonneg_left hbulk hC1
  have hb2 := mul_le_mul_of_nonneg_left hbdry hC2
  have hb3 := mul_le_mul_of_nonneg_left hbridge hC3
  have hexp : C1 * (2 * (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
        ∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m) +
      C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))) *
        (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
        ∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m) +
      C3 * (1 / (1 - (3 : ℝ) ^ (-a)) * etaX) =
      (2 * C1 + C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
          (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
          (∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m) +
        C3 / (1 - (3 : ℝ) ^ (-a)) * etaX := by ring
  have hcont : ∑ j ∈ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j ≤
      (2 * C1 + C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
          (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
          (∑ m ∈ Finset.Ico jStar t, (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * hold m) +
        C3 / (1 - (3 : ℝ) ^ (-a)) * etaX +
        C4 * ∑ j ∈ Finset.Ico (jStar + l0) n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j := by
    linarith only [hsum, hb1, hb2, hb3, hexp]
  -- the early levels, charged to the source coefficient alone
  have hearlysum : ∑ j ∈ Finset.Ico jStar n \ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j ≤
      C4 * ∑ j ∈ Finset.Ico jStar n \ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have h := mul_le_mul_of_nonneg_left (hearly j (hsubE hj)) (hwn j)
    linarith only [h]
  -- the two regimes recombine
  have hsplitH : ∑ j ∈ Finset.Ico jStar n \ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j +
      ∑ j ∈ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j =
      ∑ j ∈ Finset.Ico jStar n, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j :=
    Finset.sum_sdiff hsubK
  have hsplitS : ∑ j ∈ Finset.Ico jStar n \ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j +
      ∑ j ∈ Finset.Ico (jStar + l0) n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j =
      ∑ j ∈ Finset.Ico jStar n, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j :=
    Finset.sum_sdiff hsubK
  have hsrcsplit : C4 * ∑ j ∈ Finset.Ico jStar n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j =
      C4 * ∑ j ∈ Finset.Ico jStar n \ Finset.Ico (jStar + l0) n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j +
        C4 * ∑ j ∈ Finset.Ico (jStar + l0) n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j := by
    rw [← hsplitS]
    ring
  linarith only [hcont, hearlysum, hsplitH, hsrcsplit]

end

end Transport
end HighContrast
end Homogenization
