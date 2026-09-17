import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakOldScaleTail
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakBadBranchWeight
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The older-scale tail of the cell-average estimate, both branches of the cutoff

The per-scale analytic bound of the cell-average estimate is
`T n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · ℰ` with `ρ = respRho γ`.  This module converts
that pointwise family bound into the two branch bounds carried by the printed tail.

On the good branch `M ≤ 1` the factor `√M` may be dropped and the discarded old scales
`n = H + 1, H + 2, …` are summed with the weight `3 ^ (-(n / 2))`; the sharp geometric
comparison already in the tree leaves the window factor `3 ^ (-(respAlpha γ · H))` and the
constant `16 / (1 - respRho γ)`.

On the bad branch `1 < M` the whole weighted sum over all scales is absorbed; splitting
`1 + √M · 3 ^ (ρ n / 2)` into its two geometric parts and using `1 - respRho γ = 2 ·
respAlpha γ` again leaves `16 / (1 - respRho γ) · K · √M · ℰ`.  Only real analysis on a
sequence appears; no cell, matrix or measure is involved.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- The good-branch majorant `3 ^ (-(n / 2)) (1 + 3 ^ (ρ n / 2))`, `n = H + 1 + j`, is
summable for `0 ≤ ρ < 1`: the crude comparison `≤ 2 · 3 ^ (-(a n))` with
`a = (1 - ρ) / 2 ∈ (0, 1 / 2]` against a geometric series suffices. -/
private theorem h6a_good_majorant_summable (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (H : ℕ) :
    Summable (fun j : ℕ => (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
      (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2))) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3one : (1 : ℝ) ≤ 3 := by norm_num
  set a : ℝ := (1 - ρ) / 2 with ha
  have ha_le : a ≤ 1 / 2 := by rw [ha]; linarith
  set r : ℝ := (3 : ℝ) ^ (-a) with hr
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos h3pos _).le
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by rw [ha]; linarith)
  have hg : Summable (fun j : ℕ => (2 * (3 : ℝ) ^ (-(a * ((H : ℝ) + 1)))) * r ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
  · exact mul_nonneg (Real.rpow_pos_of_pos h3pos _).le
      (by have h := Real.rpow_pos_of_pos h3pos (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)
          linarith)
  · set n : ℝ := (H : ℝ) + 1 + (j : ℝ) with hn
    have hn0 : 0 ≤ n := by rw [hn]; positivity
    have h1 : (3 : ℝ) ^ (-(n / 2)) ≤ (3 : ℝ) ^ (-(a * n)) := by
      apply Real.rpow_le_rpow_of_exponent_le h3one
      have h : a * n ≤ (1 / 2) * n := mul_le_mul_of_nonneg_right ha_le hn0
      linarith
    have h2 : (3 : ℝ) ^ (-(n / 2)) * (3 : ℝ) ^ (ρ * n / 2)
        = (3 : ℝ) ^ (-(a * n)) := by
      rw [← Real.rpow_add h3pos]
      congr 1
      rw [ha]; ring
    have hsplit : (3 : ℝ) ^ (-(a * n)) = (3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) * r ^ j := by
      rw [hr]
      have he : -(a * n) = -(a * ((H : ℝ) + 1)) + (-(a * (j : ℝ))) := by rw [hn]; ring
      rw [he, Real.rpow_add h3pos]
      rw [show -(a * (j : ℝ)) = (-a) * (j : ℝ) by ring,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-a) (j : ℝ), Real.rpow_natCast]
    calc (3 : ℝ) ^ (-(n / 2)) * (1 + (3 : ℝ) ^ (ρ * n / 2))
        = (3 : ℝ) ^ (-(n / 2)) + (3 : ℝ) ^ (-(n / 2)) * (3 : ℝ) ^ (ρ * n / 2) := by ring
      _ = (3 : ℝ) ^ (-(n / 2)) + (3 : ℝ) ^ (-(a * n)) := by rw [h2]
      _ ≤ (3 : ℝ) ^ (-(a * n)) + (3 : ℝ) ^ (-(a * n)) := by linarith [h1]
      _ = 2 * (3 : ℝ) ^ (-(a * n)) := by ring
      _ = (2 * (3 : ℝ) ^ (-(a * ((H : ℝ) + 1)))) * r ^ j := by rw [hsplit]; ring

/-- The good branch of the older-scale tail: a nonnegative per-scale family obeying
`T n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · ℰ`, with `M ≤ 1`, has its `3 ^ (-(n / 2))`
weighted tail from `H + 1` on bounded by `16 / (1 - respRho γ) · K ·
3 ^ (-(respAlpha γ · H)) · ℰ`. -/
theorem h6a_tail_good_le {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (H : ℕ) {K En M : ℝ}
    (hK : 0 ≤ K) (hEn : 0 ≤ En) (hM : 0 ≤ M) (hgood : M ≤ 1)
    (T : ℕ → ℝ) (hT0 : ∀ n, 0 ≤ T n)
    (hT : ∀ n, T n ≤ Real.sqrt 2 * K *
      (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) * En) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j)
      ≤ 16 / (1 - respRho γ) * K * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) * En := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hρ0 : 0 ≤ respRho γ := by rw [respRho]; linarith [hγ.1]
  have hρ1 : respRho γ < 1 := by rw [respRho]; linarith [hγ.2]
  have hαeq : (1 - respRho γ) / 2 = respAlpha γ := by rw [respAlpha, respRho]; ring
  have h1mρ : 0 < 1 - respRho γ := by linarith
  have hsqM : (Real.sqrt M) ^ 2 ≤ 1 := by rw [Real.sq_sqrt hM]; exact hgood
  have hsqrt_le : Real.sqrt M ≤ 1 :=
    le_of_sq_le_sq (by simpa using hsqM) (by norm_num)
  set G : ℕ → ℝ := fun j => (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
      (1 + (3 : ℝ) ^ (respRho γ * ((H : ℝ) + 1 + (j : ℝ)) / 2)) with hG
  have hG_summ : Summable G := by
    rw [hG]
    exact h6a_good_majorant_summable (respRho γ) hρ0 hρ1 H
  have hf_nonneg : ∀ j : ℕ,
      0 ≤ (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j) := by
    intro j
    exact mul_nonneg (Real.rpow_pos_of_pos h3pos _).le (hT0 _)
  have hpoint : ∀ j : ℕ,
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j)
        ≤ Real.sqrt 2 * K * En * G j := by
    intro j
    set x : ℝ := (H : ℝ) + 1 + (j : ℝ) with hx
    have hTj := hT (H + 1 + j)
    rw [show ((H + 1 + j : ℕ) : ℝ) = x by rw [hx]; push_cast; ring] at hTj
    have hpowpos : 0 < (3 : ℝ) ^ (respRho γ * x / 2) := Real.rpow_pos_of_pos h3pos _
    have hsq : Real.sqrt M * (3 : ℝ) ^ (respRho γ * x / 2)
        ≤ (3 : ℝ) ^ (respRho γ * x / 2) := by
      calc Real.sqrt M * (3 : ℝ) ^ (respRho γ * x / 2)
          ≤ 1 * (3 : ℝ) ^ (respRho γ * x / 2) :=
            mul_le_mul_of_nonneg_right hsqrt_le hpowpos.le
        _ = (3 : ℝ) ^ (respRho γ * x / 2) := by ring
    have hinner : Real.sqrt 2 * K * (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * x / 2)) * En
        ≤ Real.sqrt 2 * K * (1 + (3 : ℝ) ^ (respRho γ * x / 2)) * En := by
      have hs2K : 0 ≤ Real.sqrt 2 * K := mul_nonneg (Real.sqrt_nonneg 2) hK
      have hstep : (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * x / 2))
          ≤ (1 + (3 : ℝ) ^ (respRho γ * x / 2)) := by linarith [hsq]
      calc Real.sqrt 2 * K * (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * x / 2)) * En
          = (Real.sqrt 2 * K)
              * ((1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * x / 2)) * En) := by ring
        _ ≤ (Real.sqrt 2 * K) * ((1 + (3 : ℝ) ^ (respRho γ * x / 2)) * En) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep hEn) hs2K
        _ = Real.sqrt 2 * K * (1 + (3 : ℝ) ^ (respRho γ * x / 2)) * En := by ring
    have hw : 0 ≤ (3 : ℝ) ^ (-(x / 2)) := (Real.rpow_pos_of_pos h3pos _).le
    calc (3 : ℝ) ^ (-(x / 2)) * T (H + 1 + j)
        ≤ (3 : ℝ) ^ (-(x / 2)) * (Real.sqrt 2 * K *
            (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * x / 2)) * En) :=
          mul_le_mul_of_nonneg_left hTj hw
      _ ≤ (3 : ℝ) ^ (-(x / 2)) * (Real.sqrt 2 * K *
            (1 + (3 : ℝ) ^ (respRho γ * x / 2)) * En) :=
          mul_le_mul_of_nonneg_left hinner hw
      _ = Real.sqrt 2 * K * En * G j := by
          simp only [hG]
          rw [← hx]
          ring
  have hf_summ : Summable (fun j : ℕ =>
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j)) :=
    Summable.of_nonneg_of_le hf_nonneg hpoint (hG_summ.mul_left _)
  have hmono : (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j))
      ≤ ∑' j : ℕ, Real.sqrt 2 * K * En * G j :=
    hf_summ.tsum_le_tsum hpoint (hG_summ.mul_left _)
  have hval : (∑' j : ℕ, Real.sqrt 2 * K * En * G j)
      = Real.sqrt 2 * K * En * ∑' j : ℕ, G j := tsum_mul_left
  set θ : ℝ := (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) with hθ
  have hTail : (∑' j : ℕ, G j) ≤ 6 / (1 - respRho γ) * θ := by
    rw [hG]
    have h := h6a_oldScale_tail_le (respRho γ) hρ0 hρ1 H
    rw [hαeq, ← hθ] at h
    exact h
  have hθ0 : 0 ≤ θ := (Real.rpow_pos_of_pos h3pos _).le
  have hsqrt2_le : Real.sqrt 2 ≤ 2 :=
    le_of_sq_le_sq
      (by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]; norm_num)
      (by norm_num)
  have h6sqrt : Real.sqrt 2 * 6 ≤ 16 := by linarith
  have hfinal : Real.sqrt 2 * K * En * (6 / (1 - respRho γ) * θ)
      ≤ 16 / (1 - respRho γ) * K * θ * En := by
    have hX : 0 ≤ K * En * θ / (1 - respRho γ) :=
      div_nonneg (mul_nonneg (mul_nonneg hK hEn) hθ0) h1mρ.le
    rw [show Real.sqrt 2 * K * En * (6 / (1 - respRho γ) * θ)
          = (Real.sqrt 2 * 6) * (K * En * θ / (1 - respRho γ)) by ring,
        show 16 / (1 - respRho γ) * K * θ * En
          = 16 * (K * En * θ / (1 - respRho γ)) by ring]
    exact mul_le_mul_of_nonneg_right h6sqrt hX
  calc (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j))
      ≤ ∑' j : ℕ, Real.sqrt 2 * K * En * G j := hmono
    _ = Real.sqrt 2 * K * En * ∑' j : ℕ, G j := hval
    _ ≤ Real.sqrt 2 * K * En * (6 / (1 - respRho γ) * θ) :=
          mul_le_mul_of_nonneg_left hTail
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hK) hEn)
    _ ≤ 16 / (1 - respRho γ) * K * θ * En := hfinal

/-- The bad branch of the older-scale tail: a nonnegative per-scale family obeying
`T n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · ℰ`, with `1 < M`, has its `3 ^ (-(n / 2))`
weighted sum over all scales bounded by `16 / (1 - respRho γ) · K · √M · ℰ`. -/
theorem h6a_tail_bad_le {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) {K En M : ℝ}
    (hK : 0 ≤ K) (hEn : 0 ≤ En) (hbad : 1 < M)
    (T : ℕ → ℝ) (hT0 : ∀ n, 0 ≤ T n)
    (hT : ∀ n, T n ≤ Real.sqrt 2 * K *
      (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) * En) :
    ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n
      ≤ 16 / (1 - respRho γ) * K * Real.sqrt M * En := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hαpos : 0 < respAlpha γ := by rw [respAlpha]; linarith [hγ.2]
  have hαle1 : respAlpha γ ≤ 1 := by rw [respAlpha]; linarith [hγ.1]
  have hαle_half : respAlpha γ ≤ 1 / 2 := by rw [respAlpha]; linarith [hγ.1]
  have hαle_quarter : respAlpha γ ≤ 1 / 4 := by rw [respAlpha]; linarith [hγ.1]
  have hs1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr (le_of_lt hbad)
  have hs0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hrα0 : 0 ≤ (3 : ℝ) ^ (-(respAlpha γ)) := (Real.rpow_pos_of_pos h3pos _).le
  have hrα1 : (3 : ℝ) ^ (-(respAlpha γ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set A : ℝ := (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ with hAdef
  set B : ℝ := (1 - (3 : ℝ) ^ (-(respAlpha γ)))⁻¹ with hBdef
  have hterm1 : ∀ n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2))
      = ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
    intro n
    rw [show -((n : ℝ) / 2) = (-(1 / 2 : ℝ)) * (n : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have htermα : ∀ n : ℕ, (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ)))
      = ((3 : ℝ) ^ (-(respAlpha γ))) ^ n := by
    intro n
    rw [show -(respAlpha γ * (n : ℝ)) = (-(respAlpha γ)) * (n : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have hg1_summ : Summable (fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2))) := by
    rw [show (fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)))
          = (fun n : ℕ => ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) by funext n; exact hterm1 n]
    exact summable_geometric_of_lt_one
      ((Real.rpow_pos_of_pos h3pos _).le)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hgα_summ : Summable (fun n : ℕ => (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ)))) := by
    rw [show (fun n : ℕ => (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ))))
          = (fun n : ℕ => ((3 : ℝ) ^ (-(respAlpha γ))) ^ n) by funext n; exact htermα n]
    exact summable_geometric_of_lt_one hrα0 hrα1
  have hg2_summ : Summable (fun n : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ)))) := hgα_summ.mul_left _
  have hg1_eq : (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2))) = A := by
    rw [hAdef]
    have h := h6a_geom_sum_rpow (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [show ∀ n : ℕ, -((n : ℝ) / 2) = -((1 / 2 : ℝ) * (n : ℝ)) by
      intro n; ring] using h
  have hgα_eq : (∑' n : ℕ, (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ)))) = B := by
    rw [hBdef]
    exact h6a_geom_sum_rpow (respAlpha γ) hαpos
  set G : ℕ → ℝ := fun n => Real.sqrt 2 * K * En *
      ((3 : ℝ) ^ (-((n : ℝ) / 2))
        + Real.sqrt M * (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ)))) with hG
  have hG_summ : Summable G := by
    rw [hG]
    have hgeom : Summable (fun n : ℕ =>
        (Real.sqrt 2 * K * En * (1 + Real.sqrt M)) * ((3 : ℝ) ^ (-(respAlpha γ))) ^ n) :=
      (summable_geometric_of_lt_one hrα0 hrα1).mul_left _
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
    · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hK) hEn)
        (add_nonneg (Real.rpow_pos_of_pos h3pos _).le
          (mul_nonneg hs0 (Real.rpow_pos_of_pos h3pos _).le))
    · have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : (3 : ℝ) ^ (-((n : ℝ) / 2)) ≤ ((3 : ℝ) ^ (-(respAlpha γ))) ^ n := by
        rw [← htermα]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        have h : respAlpha γ * (n : ℝ) ≤ (1 / 2) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hαle_half hn0
        linarith
      have hsum : (3 : ℝ) ^ (-((n : ℝ) / 2))
            + Real.sqrt M * (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ)))
          ≤ (1 + Real.sqrt M) * ((3 : ℝ) ^ (-(respAlpha γ))) ^ n := by
        rw [htermα]
        calc (3 : ℝ) ^ (-((n : ℝ) / 2))
              + Real.sqrt M * ((3 : ℝ) ^ (-(respAlpha γ))) ^ n
            ≤ ((3 : ℝ) ^ (-(respAlpha γ))) ^ n
              + Real.sqrt M * ((3 : ℝ) ^ (-(respAlpha γ))) ^ n := add_le_add h1 le_rfl
          _ = (1 + Real.sqrt M) * ((3 : ℝ) ^ (-(respAlpha γ))) ^ n := by ring
      calc Real.sqrt 2 * K * En *
            ((3 : ℝ) ^ (-((n : ℝ) / 2))
              + Real.sqrt M * (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ))))
          ≤ (Real.sqrt 2 * K * En)
              * ((1 + Real.sqrt M) * ((3 : ℝ) ^ (-(respAlpha γ))) ^ n) :=
            mul_le_mul_of_nonneg_left hsum
              (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hK) hEn)
        _ = (Real.sqrt 2 * K * En * (1 + Real.sqrt M)) * ((3 : ℝ) ^ (-(respAlpha γ))) ^ n := by
            ring
  have hf_nonneg : ∀ n : ℕ, 0 ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n := by
    intro n
    exact mul_nonneg (Real.rpow_pos_of_pos h3pos _).le (hT0 n)
  have hpoint : ∀ n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n ≤ G n := by
    intro n
    have hpow : (3 : ℝ) ^ (-((n : ℝ) / 2)) * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)
        = (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ))) := by
      rw [← Real.rpow_add h3pos]
      congr 1
      rw [respAlpha, respRho]
      ring
    have hw : 0 ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) := (Real.rpow_pos_of_pos h3pos _).le
    calc (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n
        ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (Real.sqrt 2 * K *
              (1 + Real.sqrt M * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) * En) :=
          mul_le_mul_of_nonneg_left (hT n) hw
      _ = Real.sqrt 2 * K * En *
            ((3 : ℝ) ^ (-((n : ℝ) / 2))
              + Real.sqrt M * (3 : ℝ) ^ (-(respAlpha γ * (n : ℝ)))) := by
          rw [← hpow]; ring
      _ = G n := by rw [hG]
  have hGval : (∑' n : ℕ, G n)
      = Real.sqrt 2 * K * En * (A + Real.sqrt M * B) := by
    rw [hG]
    rw [tsum_mul_left]
    rw [hg1_summ.tsum_add hg2_summ]
    rw [tsum_mul_left]
    rw [hg1_eq, hgα_eq]
  have hA : A ≤ 3 := by rw [hAdef]; exact h6a_inv_one_sub_rpow_half_le
  have hB : B ≤ 3 / respAlpha γ := by
    rw [hBdef]
    exact h6a_inv_one_sub_rpow_le (respAlpha γ) hαpos hαle1
  have hsumAB : Real.sqrt 2 * (A + Real.sqrt M * B)
      ≤ Real.sqrt 2 * 3 + Real.sqrt 2 * (Real.sqrt M * (3 / respAlpha γ)) := by
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1 : Real.sqrt 2 * A ≤ Real.sqrt 2 * 3 := mul_le_mul_of_nonneg_left hA hs2
    have h2 : Real.sqrt M * B ≤ Real.sqrt M * (3 / respAlpha γ) :=
      mul_le_mul_of_nonneg_left hB hs0
    have h3 : Real.sqrt 2 * (Real.sqrt M * B)
        ≤ Real.sqrt 2 * (Real.sqrt M * (3 / respAlpha γ)) :=
      mul_le_mul_of_nonneg_left h2 hs2
    rw [mul_add]
    exact add_le_add h1 h3
  have hsqrt2_le : Real.sqrt 2 ≤ 2 :=
    le_of_sq_le_sq
      (by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]; norm_num)
      (by norm_num)
  have hkey : Real.sqrt 2 * 3 * respAlpha γ ≤ (8 - Real.sqrt 2 * 3) * Real.sqrt M := by
    have h1 : Real.sqrt 2 * 3 * respAlpha γ ≤ Real.sqrt 2 * 3 * (1 / 4) :=
      mul_le_mul_of_nonneg_left hαle_quarter (by positivity)
    have h2 : Real.sqrt 2 * 3 * (1 / 4) ≤ 2 := by linarith only [hsqrt2_le]
    have h4 : (2 : ℝ) ≤ 8 - Real.sqrt 2 * 3 := by linarith only [hsqrt2_le]
    have h3 : (2 : ℝ) ≤ (8 - Real.sqrt 2 * 3) * Real.sqrt M := by
      calc (2 : ℝ) = 2 * 1 := by ring
        _ ≤ (8 - Real.sqrt 2 * 3) * Real.sqrt M :=
            mul_le_mul h4 hs1 (by norm_num) (by linarith)
    linarith
  have htarget : Real.sqrt 2 * 3 + Real.sqrt 2 * (Real.sqrt M * (3 / respAlpha γ))
      ≤ 8 / respAlpha γ * Real.sqrt M := by
    have hmul : (Real.sqrt 2 * 3
          + Real.sqrt 2 * (Real.sqrt M * (3 / respAlpha γ))) * respAlpha γ
        ≤ (8 / respAlpha γ * Real.sqrt M) * respAlpha γ := by
      rw [show (Real.sqrt 2 * 3
              + Real.sqrt 2 * (Real.sqrt M * (3 / respAlpha γ))) * respAlpha γ
            = Real.sqrt 2 * 3 * respAlpha γ + Real.sqrt 2 * 3 * Real.sqrt M by
            field_simp [hαpos.ne'],
          show (8 / respAlpha γ * Real.sqrt M) * respAlpha γ = 8 * Real.sqrt M by
            field_simp [hαpos.ne']]
      linarith [hkey]
    exact le_of_mul_le_mul_right hmul hαpos
  have hscalar : Real.sqrt 2 * (A + Real.sqrt M * B)
      ≤ 16 / (1 - respRho γ) * Real.sqrt M := by
    have h8 : 16 / (1 - respRho γ) = 8 / respAlpha γ := by
      rw [show 1 - respRho γ = 2 * respAlpha γ by rw [respAlpha, respRho]; ring]
      ring_nf
    rw [h8]
    exact hsumAB.trans htarget
  have hfin : Real.sqrt 2 * K * En * (A + Real.sqrt M * B)
      ≤ 16 / (1 - respRho γ) * K * Real.sqrt M * En := by
    have hKEn : 0 ≤ K * En := mul_nonneg hK hEn
    have h := mul_le_mul_of_nonneg_left hscalar hKEn
    calc Real.sqrt 2 * K * En * (A + Real.sqrt M * B)
        = (K * En) * (Real.sqrt 2 * (A + Real.sqrt M * B)) := by ring
      _ ≤ (K * En) * (16 / (1 - respRho γ) * Real.sqrt M) := h
      _ = 16 / (1 - respRho γ) * K * Real.sqrt M * En := by ring
  have hf_summ : Summable (fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n) :=
    Summable.of_nonneg_of_le hf_nonneg hpoint hG_summ
  calc (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n)
      ≤ ∑' n : ℕ, G n := hf_summ.tsum_le_tsum hpoint hG_summ
    _ = Real.sqrt 2 * K * En * (A + Real.sqrt M * B) := hGval
    _ ≤ 16 / (1 - respRho γ) * K * Real.sqrt M * En := hfin

end

end Homogenization.HighContrast.Multiscale
