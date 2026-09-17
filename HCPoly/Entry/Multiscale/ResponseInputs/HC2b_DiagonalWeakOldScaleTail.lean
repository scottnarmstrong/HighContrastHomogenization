import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Real arithmetic for the discarded old scales on the good branch

Below the response window the cell-average lemma discards the scales above the cutoff `H` and
pays `3 ^ (-((1 - ρ) / 2) * H)` for them.  On the good branch each discarded scale `n` carries
the factor `1 + 3 ^ (ρ n / 2)`, so the `3 ^ (-(n / 2))`-weighted tail
`∑ j, 3 ^ (-(n / 2)) * (1 + 3 ^ (ρ n / 2))`, with `n = H + 1 + j`, is controlled by
`6 / (1 - ρ)` times the window weight.  This leaf module records the three real inequalities
realizing that step for `0 ≤ ρ < 1`.  No cell, matrix or measure appears.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- The sharp geometric coefficient at `a = (1 - ρ) / 2`: the pointwise factor `2` leaves an
extra `3 ^ (-a)` behind the geometric ratio, and the combined bound
`2 * 3 ^ (-a) * (1 - 3 ^ (-a))⁻¹ ≤ 3 / a` holds for every `a > 0`. -/
private theorem h6a_oldScale_sharp (a : ℝ) (ha0 : 0 < a) :
    2 * (3 : ℝ) ^ (-a) * (1 - (3 : ℝ) ^ (-a))⁻¹ ≤ 3 / a := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3nonneg : (0 : ℝ) ≤ 3 := by norm_num
  have hlog_gt_one : 1 < Real.log 3 := by
    have h3 : Real.exp 1 < 3 := by
      have h9 := Real.exp_one_lt_d9
      linarith
    have h4 := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at h4
  have hlog23 : (2 : ℝ) / 3 ≤ Real.log 3 := by linarith
  have hkey : (3 : ℝ) ^ (-a) * (3 + 2 * a) ≤ 3 := by
    have ha' : 0 ≤ a := ha0.le
    have hexp : a * Real.log 3 + 1 ≤ Real.exp (a * Real.log 3) :=
      Real.add_one_le_exp _
    have hrpow : (3 : ℝ) ^ a = Real.exp (a * Real.log 3) := by
      rw [Real.rpow_def_of_pos h3pos a]
      congr 1
      ring
    have hle : 1 + (2 : ℝ) / 3 * a ≤ (3 : ℝ) ^ a := by
      calc 1 + (2 : ℝ) / 3 * a = 1 + a * (2 / 3) := by ring
        _ ≤ 1 + a * Real.log 3 := by
              have hm := mul_le_mul_of_nonneg_left hlog23 ha'
              linarith
        _ = a * Real.log 3 + 1 := by ring
        _ ≤ Real.exp (a * Real.log 3) := hexp
        _ = (3 : ℝ) ^ a := hrpow.symm
    have h3a_pos : 0 < (3 : ℝ) ^ a := Real.rpow_pos_of_pos h3pos a
    have h2 : 3 + 2 * a ≤ 3 * (3 : ℝ) ^ a := by
      calc 3 + 2 * a = 3 * (1 + (2 : ℝ) / 3 * a) := by ring
        _ ≤ 3 * (3 : ℝ) ^ a := mul_le_mul_of_nonneg_left hle (by norm_num)
    have hneg : (3 : ℝ) ^ (-a) = ((3 : ℝ) ^ a)⁻¹ := Real.rpow_neg h3nonneg a
    rw [hneg, inv_mul_eq_div]
    exact (div_le_iff₀ h3a_pos).mpr h2
  have hsub : 2 * a * (3 : ℝ) ^ (-a) ≤ 3 * (1 - (3 : ℝ) ^ (-a)) := by
    have h := hkey
    have hexpand : (3 : ℝ) ^ (-a) * (3 + 2 * a)
        = 3 * (3 : ℝ) ^ (-a) + 2 * a * (3 : ℝ) ^ (-a) := by ring
    rw [hexpand] at h
    linarith
  have hlt1 : (3 : ℝ) ^ (-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hpos1mr : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  have hdiv : 2 * (3 : ℝ) ^ (-a) ≤ (3 / a) * (1 - (3 : ℝ) ^ (-a)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
    linarith [hsub]
  have hstep : (2 * (3 : ℝ) ^ (-a)) * (1 - (3 : ℝ) ^ (-a))⁻¹
      ≤ ((3 / a) * (1 - (3 : ℝ) ^ (-a))) * (1 - (3 : ℝ) ^ (-a))⁻¹ :=
    mul_le_mul_of_nonneg_right hdiv (inv_nonneg.mpr hpos1mr.le)
  have hrhs : ((3 / a) * (1 - (3 : ℝ) ^ (-a))) * (1 - (3 : ℝ) ^ (-a))⁻¹ = 3 / a := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos1mr), mul_one]
  exact hstep.trans_eq hrhs

/-- The pointwise good-branch decay: for `0 ≤ ρ < 1` and `x ≥ 0`, the weight
`3 ^ (-(x / 2))` applied to `1 + 3 ^ (ρ x / 2)` is bounded by
`2 * 3 ^ (-((1 - ρ) / 2 * x))`. -/
theorem h6a_oldScale_pointwise (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x : ℝ) (hx : 0 ≤ x) :
    (3 : ℝ) ^ (-(x / 2)) * (1 + (3 : ℝ) ^ (ρ * x / 2))
      ≤ 2 * (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by
  have _hρ1 : ρ < 1 := hρ1
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3one : (1 : ℝ) ≤ 3 := by norm_num
  have hcoef : (1 - ρ) / 2 ≤ 1 / 2 := by linarith
  have hle_exp : -(x / 2) ≤ -((1 - ρ) / 2 * x) := by
    have h : (1 - ρ) / 2 * x ≤ (1 / 2) * x := mul_le_mul_of_nonneg_right hcoef hx
    linarith
  have hA : (3 : ℝ) ^ (-(x / 2)) ≤ (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) :=
    Real.rpow_le_rpow_of_exponent_le h3one hle_exp
  have hB : (3 : ℝ) ^ (-(x / 2)) * (3 : ℝ) ^ (ρ * x / 2)
      = (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by
    rw [← Real.rpow_add h3pos]
    congr 1
    ring
  calc (3 : ℝ) ^ (-(x / 2)) * (1 + (3 : ℝ) ^ (ρ * x / 2))
      = (3 : ℝ) ^ (-(x / 2))
          + (3 : ℝ) ^ (-(x / 2)) * (3 : ℝ) ^ (ρ * x / 2) := by ring
    _ = (3 : ℝ) ^ (-(x / 2)) + (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by rw [hB]
    _ ≤ (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) + (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by
          linarith [hA]
    _ = 2 * (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by ring

/-- The good-branch discarded tail: for `0 ≤ ρ < 1`, the `3 ^ (-(n / 2))`-weighted sum of
`1 + 3 ^ (ρ n / 2)` over the scales `n = H + 1, H + 2, …` is bounded by `6 / (1 - ρ)` times
the window weight `3 ^ (-((1 - ρ) / 2) * H)`. -/
theorem h6a_oldScale_tail_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (H : ℕ) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2))
      ≤ 6 / (1 - ρ) * (3 : ℝ) ^ (-((1 - ρ) / 2 * (H : ℝ))) := by
  set a : ℝ := (1 - ρ) / 2 with ha
  set r : ℝ := (3 : ℝ) ^ (-a) with hr
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have ha_pos : 0 < a := by rw [ha]; linarith
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact (Real.rpow_pos_of_pos h3pos (-a)).le
  have hr_lt_one : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  set c : ℝ := 2 * (3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) with hc
  have hc_expand : c = (3 : ℝ) ^ (-(a * (H : ℝ))) * (2 * (3 : ℝ) ^ (-a)) := by
    rw [hc]
    have h : -(a * ((H : ℝ) + 1)) = -(a * (H : ℝ)) + (-a) := by ring
    rw [h, Real.rpow_add h3pos]
    ring
  have hg_summ : Summable (fun j : ℕ => c * r ^ j) :=
    (summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left c
  have hf_nonneg : ∀ j : ℕ,
      0 ≤ (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)) := by
    intro j
    apply mul_nonneg
    · exact (Real.rpow_pos_of_pos h3pos _).le
    · have hpos : 0 < (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2) :=
        Real.rpow_pos_of_pos h3pos _
      linarith
  have hle : ∀ j : ℕ,
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)) ≤ c * r ^ j := by
    intro j
    set x : ℝ := (H : ℝ) + 1 + (j : ℝ) with hx
    have hx_nonneg : 0 ≤ x := by rw [hx]; positivity
    have hp := h6a_oldScale_pointwise ρ hρ0 hρ1 x hx_nonneg
    have hpow : (3 : ℝ) ^ (-(a * (j : ℝ))) = r ^ j := by
      rw [hr]
      have h1 : -(a * (j : ℝ)) = (-a) * (j : ℝ) := by ring
      rw [h1, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-a) (j : ℝ), Real.rpow_natCast]
    have hsplit : (3 : ℝ) ^ (-((1 - ρ) / 2 * x))
        = (3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) * r ^ j := by
      have he : -((1 - ρ) / 2 * x) = -(a * ((H : ℝ) + 1)) + (-(a * (j : ℝ))) := by
        rw [← ha, hx]
        ring
      rw [he, Real.rpow_add h3pos, hpow]
    calc (3 : ℝ) ^ (-(x / 2)) * (1 + (3 : ℝ) ^ (ρ * x / 2))
        ≤ 2 * (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := hp
      _ = 2 * ((3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) * r ^ j) := by rw [hsplit]
      _ = c * r ^ j := by rw [hc]; ring
  have hf_summ : Summable (fun j : ℕ =>
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2))) :=
    Summable.of_nonneg_of_le hf_nonneg hle hg_summ
  have hmono : (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)))
      ≤ ∑' j : ℕ, c * r ^ j :=
    hf_summ.tsum_le_tsum hle hg_summ
  have htsum_g : (∑' j : ℕ, c * r ^ j) = c * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
  have hcoef : (3 : ℝ) / a = 6 / (1 - ρ) := by
    have hne : (1 : ℝ) - ρ ≠ 0 := by linarith
    rw [ha]
    field_simp [hne]
    ring
  calc (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)))
      ≤ ∑' j : ℕ, c * r ^ j := hmono
    _ = c * (1 - r)⁻¹ := htsum_g
    _ = (3 : ℝ) ^ (-(a * (H : ℝ))) * (2 * (3 : ℝ) ^ (-a) * (1 - r)⁻¹) := by
          rw [hc_expand]; ring
    _ ≤ (3 : ℝ) ^ (-(a * (H : ℝ))) * (3 / a) :=
          mul_le_mul_of_nonneg_left (h6a_oldScale_sharp a ha_pos)
            (Real.rpow_pos_of_pos h3pos _).le
    _ = 6 / (1 - ρ) * (3 : ℝ) ^ (-(a * (H : ℝ))) := by rw [hcoef]; ring

end

end Homogenization.HighContrast.Multiscale
