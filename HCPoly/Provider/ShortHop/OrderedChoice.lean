/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.ErrorEnvelopes

/-!
# The ordered choice of the short test

`p.successful.short.bridge` fixes five thresholds before the law, in
the printed order: the hop length `ℓ₀`, the source allowance `τ_src`, the
determinant tolerance `δ_short`, the drift tolerance `η_pre`, and the cutoff
coefficient `B`.  This file proves the first two steps of that order.

The hop length is chosen first.  All four requirements involving `ℓ₀` among the
constants fixed for the bridge test, the two common lower bounds `L_common` and
`L_tr`, and the two floors
`η_br^{(0)}(ℓ₀) ≤ η_x/2` and `𝔡_new^{(0)}(ℓ₀) ≤ η_new/2` are simultaneously
satisfiable, because the first four are lower bounds on `ℓ₀` and the last two
ask a fixed multiple of `CK_hop3^{-ℓ₀}` to be small.

The three small thresholds come next.  Since the six error envelopes are
monotone in each argument and continuous, and the two composite envelopes sit
strictly below their allowances at the origin, one radius serves for all three:
on the box it cuts out, the bridge-error envelope stays below `η_x` and the
new-grid drift envelope below `η_new`.  This is the pair of threshold
inequalities the proposition exports.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open Real

noncomputable section

/-! ## The two elementary selections -/

/-- Powers of one third are eventually below any positive allowance. -/
private theorem exists_rpow_le {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (3 : ℝ) ^ (-(n : ℝ)) ≤ eps := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (1 : ℝ) / 3 < 1)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (3 : ℝ) ^ (-(n : ℝ)) = ((1 : ℝ) / 3) ^ n := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [h1]
  exact le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hN.le

/-- The drift exponent of the initialization is positive below the growth
exponent one. -/
theorem initExpRhoDr_pos {g : ℝ} (hg : g < 1) : 0 < initExpRhoDr g := by
  have h : (0 : ℝ) < 1 - g := by linarith only [hg]
  simp only [initExpRhoDr, initExpA]
  linarith only [h]

/-! ## The hop length -/

/-- **The choice of `ℓ₀`.**  A single hop length meets both common lower
bounds, all four requirements that mention it among the constants fixed for the
bridge test, and the two floors of the proof: at the origin the bridge-error
envelope is below half the near-isometry allowance and the new-grid drift
envelope below half the drift allowance.

The hop length is unconstrained by the sign of the projective jump: the strict
requirement is a lower bound on `ℓ₀` that the ceiling meets whatever the value
of `c_hop`, so positivity of the jump is not needed here. -/
theorem exists_shortScale (d Lcommon Ltr : ℕ) {g chop etaNew etaX C Khop : ℝ}
    (hg : g < 1) (hetaNew : 0 < etaNew) (hetaX : 0 < etaX)
    (hC : 0 < C) (hKhop : 1 ≤ Khop) :
    ∃ l0 : ℕ, max Lcommon Ltr ≤ l0 ∧
      C * (1 + Real.log Khop) ≤ (l0 : ℝ) ∧
      C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2 ∧
      2 * chop < initExpRhoDr g * (l0 : ℝ) * Real.log 3 / 2 ∧
      shortBridgeErr d C Khop (initExpRhoDr g) (l0 : ℤ) 0 0 0 0 ≤ etaX / 2 ∧
      shortNewDrift d C Khop (initExpRhoDr g) (l0 : ℤ) 0 0 0 0 ≤ etaNew / 2 := by
  have hrho : 0 < initExpRhoDr g := initExpRhoDr_pos hg
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hCK : 0 < C * Khop := mul_pos hC (lt_of_lt_of_le zero_lt_one hKhop)
  have hcoef : 0 < 2 * C + 1 := by linarith only [hC]
  -- the allowance the geometric factor must meet
  set eps : ℝ := min (1 / 2) (min (etaX / 4) (etaNew / (2 * (2 * C + 1)))) with heps
  have heps0 : 0 < eps := by
    refine lt_min (by norm_num) (lt_min (by linarith only [hetaX]) ?_)
    positivity
  obtain ⟨N, hN⟩ := exists_rpow_le (div_pos heps0 hCK)
  -- the three lower bounds
  refine ⟨max (max Lcommon Ltr) (max N (max ⌈C * (1 + Real.log Khop)⌉₊
      (⌈4 * chop / (initExpRhoDr g * Real.log 3)⌉₊ + 1))), le_max_left _ _, ?_⟩
  set l0 : ℕ := max (max Lcommon Ltr) (max N (max ⌈C * (1 + Real.log Khop)⌉₊
      (⌈4 * chop / (initExpRhoDr g * Real.log 3)⌉₊ + 1))) with hl0
  have hNl : N ≤ l0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hceil : ⌈C * (1 + Real.log Khop)⌉₊ ≤ l0 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hstrict : ⌈4 * chop / (initExpRhoDr g * Real.log 3)⌉₊ + 1 ≤ l0 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  -- the geometric factor
  have hgeom : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ eps := by
    have h := hN l0 hNl
    have := mul_le_mul_of_nonneg_left h hCK.le
    calc C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ C * Khop * (eps / (C * Khop)) := this
      _ = eps := by field_simp
  have hcast : (((l0 : ℕ) : ℤ) : ℝ) = (l0 : ℝ) := by push_cast; ring
  have hgeomZ : C * Khop * (3 : ℝ) ^ (-(((l0 : ℕ) : ℤ) : ℝ)) ≤ eps := by rwa [hcast]
  have hhalf : C * Khop * (3 : ℝ) ^ (-(((l0 : ℕ) : ℤ) : ℝ)) ≤ 1 / 2 :=
    le_trans hgeomZ (le_trans (min_le_left _ _) le_rfl)
  refine ⟨?_, by rw [hcast] at hhalf; exact hhalf, ?_, ?_, ?_⟩
  · exact le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  · -- the strict hop-length requirement
    have hpos : 0 < initExpRhoDr g * Real.log 3 := mul_pos hrho hlog3
    have hlt : 4 * chop / (initExpRhoDr g * Real.log 3) < (l0 : ℝ) := by
      have h1 : (4 * chop / (initExpRhoDr g * Real.log 3)) ≤
          (⌈4 * chop / (initExpRhoDr g * Real.log 3)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈4 * chop / (initExpRhoDr g * Real.log 3)⌉₊ : ℕ) : ℝ) + 1 ≤ (l0 : ℝ) := by
        exact_mod_cast hstrict
      linarith only [h1, h2]
    rw [div_lt_iff₀ hpos] at hlt
    linarith only [hlt]
  · refine le_trans (shortBridgeErr_zero_le hC.le (by linarith only [hKhop]) hhalf) ?_
    have h : eps ≤ etaX / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith only [hgeomZ, h]
  · refine le_trans (shortNewDrift_zero_le hC.le (by linarith only [hKhop]) hhalf) ?_
    have h : eps ≤ etaNew / (2 * (2 * C + 1)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_left (le_trans hgeomZ h) hcoef.le
    calc (2 * C + 1) * (C * Khop * (3 : ℝ) ^ (-(((l0 : ℕ) : ℤ) : ℝ)))
        ≤ (2 * C + 1) * (etaNew / (2 * (2 * C + 1))) := hmul
      _ = etaNew / 2 := by field_simp

/-! ## The three small thresholds -/

/-- **The two threshold inequalities.**  One positive radius serves as source
allowance, determinant tolerance and drift tolerance at once: on the box it cuts
out, the bridge-error envelope stays below the near-isometry allowance and the
new-grid drift envelope below the drift allowance.  This is the content of the
ordered choice, and the reason the source allowance is load-bearing rather than
an unconstrained positive number. -/
theorem exists_shortThresholds (d : ℕ) {C Khop rhoDr etaX etaNew : ℝ} {l0 : ℤ}
    (hC : 0 ≤ C) (hK : 0 ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2)
    (hetaX : 0 < etaX) (hetaNew : 0 < etaNew)
    (hbr : shortBridgeErr d C Khop rhoDr l0 0 0 0 0 ≤ etaX / 2)
    (hnd : shortNewDrift d C Khop rhoDr l0 0 0 0 0 ≤ etaNew / 2) :
    ∃ tau : ℝ, 0 < tau ∧
      ∀ b delta R1 R2 R3 : ℝ, 0 ≤ b → b ≤ tau → 0 ≤ delta → delta ≤ tau →
        0 ≤ R1 → R1 ≤ tau → 0 ≤ R2 → R2 ≤ tau → 0 ≤ R3 → R3 ≤ tau →
        shortBridgeErr d C Khop rhoDr l0 b delta R1 R2 ≤ etaX ∧
          shortNewDrift d C Khop rhoDr l0 b delta R2 R3 ≤ etaNew := by
  have hFc : ContinuousAt (fun t : ℝ => shortBridgeErr d C Khop rhoDr l0 t t t t) 0 :=
    continuous_shortBridgeErr_diag.continuousAt
  have hGc : ContinuousAt (fun t : ℝ => shortNewDrift d C Khop rhoDr l0 t t t t) 0 :=
    continuous_shortNewDrift_diag.continuousAt
  have hFmem : Set.Iio etaX ∈ nhds (shortBridgeErr d C Khop rhoDr l0 0 0 0 0) :=
    Iio_mem_nhds (by linarith only [hbr, hetaX])
  have hGmem : Set.Iio etaNew ∈ nhds (shortNewDrift d C Khop rhoDr l0 0 0 0 0) :=
    Iio_mem_nhds (by linarith only [hnd, hetaNew])
  obtain ⟨e1, he1, hb1⟩ := Metric.mem_nhds_iff.mp (hFc.preimage_mem_nhds hFmem)
  obtain ⟨e2, he2, hb2⟩ := Metric.mem_nhds_iff.mp (hGc.preimage_mem_nhds hGmem)
  refine ⟨min e1 e2 / 2, by positivity, fun b delta R1 R2 R3 hb hbt hd hdt hR1 hR1t hR2 hR2t
    hR3 hR3t => ?_⟩
  have htau0 : (0 : ℝ) ≤ min e1 e2 / 2 := by positivity
  have hdist1 : dist (min e1 e2 / 2) 0 < e1 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg htau0]
    have : min e1 e2 ≤ e1 := min_le_left _ _
    linarith only [this, he1]
  have hdist2 : dist (min e1 e2 / 2) 0 < e2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg htau0]
    have : min e1 e2 ≤ e2 := min_le_right _ _
    linarith only [this, he2]
  have hF : shortBridgeErr d C Khop rhoDr l0 (min e1 e2 / 2) (min e1 e2 / 2)
      (min e1 e2 / 2) (min e1 e2 / 2) < etaX := hb1 (by simpa using hdist1)
  have hG : shortNewDrift d C Khop rhoDr l0 (min e1 e2 / 2) (min e1 e2 / 2)
      (min e1 e2 / 2) (min e1 e2 / 2) < etaNew := hb2 (by simpa using hdist2)
  exact ⟨le_trans (shortBridgeErr_mono hC hK hden hb hbt hd hdt hR1 hR1t hR2t) hF.le,
    le_trans (shortNewDrift_mono hC hK hden hb hbt hd hdt hR2t hR3t) hG.le⟩

end

end ShortHop
end HighContrast
end Homogenization
