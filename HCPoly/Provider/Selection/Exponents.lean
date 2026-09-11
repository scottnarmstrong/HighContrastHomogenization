/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Frozen.FixedGridRecurrence
import HCPoly.Frozen.PortableHistory
import HCPoly.Provider.Bridge.ScaleFacts
import HCPoly.Setup.Exponents

/-!
# Exponents and the service length for the global selection

The global selector uses the fixed initialization exponents.  This file records
their arithmetic properties and chooses one service length at which both the
portable contraction factor and the drift discount have reached the sizes used
by the selector.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

/-! ## Initialization exponents -/

/-- The moment exponent chosen for initialization is even. -/
theorem initExpQ_even (d : ℕ) (g : ℝ) : Even (initExpQ d g) := by
  exact InitializationExponents.initExpQ_even d g

/-- The moment exponent chosen for initialization is at least two. -/
theorem two_le_initExpQ {d : ℕ} {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    2 ≤ initExpQ d g := by
  exact InitializationExponents.two_le_initExpQ d hg.2

/-- The history exponent `a` is positive below the growth exponent one. -/
theorem initExpA_pos {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < initExpA g := by
  exact InitializationExponents.initExpA_pos hg.2

/-- The history exponent `a` is strictly below the unused growth exponent. -/
theorem initExpA_lt_one_sub {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    initExpA g < 1 - g := by
  unfold initExpA
  linarith only [hg.2]

/-- The drift exponent is positive. -/
theorem initExpRhoDr_pos {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < initExpRhoDr g :=
  Bridge.initExpRhoDr_pos hg

/-- The maximal history exponent is strictly above the growth exponent. -/
theorem initExpRhoMax_gt {d : ℕ} {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    g < initExpRhoMax d g := by
  exact InitializationExponents.lt_initExpRhoMax d hg.2

/-- The maximal history exponent remains below one. -/
theorem initExpRhoMax_lt_one {d : ℕ} {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    initExpRhoMax d g < 1 := by
  have hden : (0 : ℝ) < 1 - g := by linarith only [hg.2]
  have hceil : 2 * ((d : ℝ) + 1) / (1 - g) ≤
      (⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ : ℝ) := Nat.le_ceil _
  have hQlarge : 4 * ((d : ℝ) + 1) / (1 - g) ≤ (initExpQ d g : ℝ) := by
    calc
      4 * ((d : ℝ) + 1) / (1 - g) =
          2 * (2 * ((d : ℝ) + 1) / (1 - g)) := by ring
      _ ≤ 2 * (⌈2 * ((d : ℝ) + 1) / (1 - g)⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left hceil (by norm_num)
      _ = (initExpQ d g : ℝ) := by unfold initExpQ; push_cast; ring
  have hQpos : (0 : ℝ) < (initExpQ d g : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_initExpQ hg))
  have ha_le_one : initExpA g ≤ 1 := by
    unfold initExpA
    linarith only [hg.1]
  have hnum : (d : ℝ) + initExpA g ≤ (d : ℝ) + 1 :=
    by linarith only [ha_le_one]
  have hscale : (d : ℝ) + 1 ≤ (1 - g) / 4 * (initExpQ d g : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hQlarge (by positivity : 0 ≤ (1 - g) / 4)
    have hid : (1 - g) / 4 * (4 * ((d : ℝ) + 1) / (1 - g)) =
        (d : ℝ) + 1 := by field_simp
    rw [hid] at hmul
    exact hmul
  have hfrac : ((d : ℝ) + initExpA g) / (initExpQ d g : ℝ) ≤
      (1 - g) / 4 := by
    rw [div_le_iff₀ hQpos]
    exact hnum.trans hscale
  unfold initExpRhoMax
  linarith only [hfrac, hden]

/-- The exponents satisfy the exact balance printed in Phase 0. -/
theorem initExp_balance {d : ℕ} {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    (initExpQ d g : ℝ) * (initExpRhoMax d g - g) - (d : ℝ) = initExpA g := by
  have hQne : (initExpQ d g : ℝ) ≠ 0 := by
    exact ne_of_gt (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_initExpQ hg)))
  unfold initExpRhoMax
  field_simp
  ring

/-- The initialization exponents meet the portable-history admissibility. -/
theorem initExp_portable_admissible {d : ℕ} {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    initExpA g ≤ (initExpQ d g : ℝ) * initExpRhoMax d g - (d : ℝ) := by
  have hbal := initExp_balance (d := d) hg
  have hgQ : 0 ≤ (initExpQ d g : ℝ) * g :=
    mul_nonneg (Nat.cast_nonneg _) hg.1
  linarith only [hbal, hgQ]

/-- The remaining summability exponent in the transport input is positive. -/
theorem initExp_summability_pos {d : ℕ} {g : ℝ} (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < ((d : ℝ) + 1) / 2 - g - initExpA g / (initExpQ d g : ℝ) := by
  have hQ : (2 : ℝ) ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast two_le_initExpQ (d := d) hg
  have hQpos : (0 : ℝ) < (initExpQ d g : ℝ) := lt_of_lt_of_le (by norm_num) hQ
  have ha0 : 0 ≤ initExpA g := (initExpA_pos hg).le
  have hdiv : initExpA g / (initExpQ d g : ℝ) ≤ initExpA g / 2 := by
    exact div_le_div_of_nonneg_left ha0 (by norm_num) hQ
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  unfold initExpA at hdiv ⊢
  linarith only [hdiv, hdR, hg.2]

/-! ## A common service length -/

/-- A power of a nonnegative number below one is eventually below any positive
allowance, uniformly after the chosen index. -/
private theorem exists_pow_le {r eps : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (heps : 0 < eps) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → r ^ n ≤ eps := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one heps hr1
  refine ⟨N, fun n hn => ?_⟩
  exact (pow_le_pow_of_le_one hr0 hr1.le hn).trans hN.le

/-- There is one positive integer service length for which the portable
contraction is at most one quarter and the drift discount at most one eighth. -/
theorem exists_serviceLength (d : ℕ) (hd : 2 ≤ d) {g Crec : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCrec : 0 < Crec) :
    ∃ h : ℤ, 1 ≤ h ∧
      lambdaPort d (initExpQ d g : ℝ) (initExpA g) Crec h ≤ 1 / 4 ∧
      (3 : ℝ) ^ (-(h : ℝ) * initExpRhoDr g) ≤ 1 / 8 := by
  let Q : ℝ := initExpQ d g
  let a : ℝ := initExpA g
  let rho : ℝ := initExpRhoDr g
  let A : ℝ := 2 ^ (Q - 1) * Crec ^ Q
  have ha : 0 < a := initExpA_pos hg
  have hrho : 0 < rho := initExpRhoDr_pos hg
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_initExpQ hg))
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hCrec _)
  let ra : ℝ := (3 : ℝ) ^ (-a)
  let rb : ℝ := (3 : ℝ) ^ (-(Q * (d : ℝ) / 2))
  let rr : ℝ := (3 : ℝ) ^ (-rho)
  have hra0 : 0 ≤ ra := Real.rpow_nonneg (by norm_num) _
  have hrb0 : 0 ≤ rb := Real.rpow_nonneg (by norm_num) _
  have hrr0 : 0 ≤ rr := Real.rpow_nonneg (by norm_num) _
  have hra1 : ra < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr ha)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  have hQd : 0 < Q * (d : ℝ) / 2 := div_pos (mul_pos hQ hdR) (by norm_num)
  have hrb1 : rb < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hQd)
  have hrr1 : rr < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hrho)
  obtain ⟨Na, hNa⟩ := exists_pow_le hra0 hra1 (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨Nb, hNb⟩ := exists_pow_le hrb0 hrb1
    (by positivity : (0 : ℝ) < 1 / (8 * A))
  obtain ⟨Nr, hNr⟩ := exists_pow_le hrr0 hrr1 (by norm_num : (0 : ℝ) < 1 / 8)
  let n : ℕ := max 1 (max Na (max Nb Nr))
  have hn1 : 1 ≤ n := le_max_left _ _
  have hna : Na ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  have hnb : Nb ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hnr : Nr ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hpa : ra ^ n ≤ (1 : ℝ) / 8 := hNa n hna
  have hpb : rb ^ n ≤ (1 : ℝ) / (8 * A) := hNb n hnb
  have hpr : rr ^ n ≤ (1 : ℝ) / 8 := hNr n hnr
  have hca : (3 : ℝ) ^ (-((n : ℤ) : ℝ) * a) = ra ^ n := by
    rw [show -((n : ℤ) : ℝ) * a = -a * (n : ℝ) by push_cast; ring]
    exact Real.rpow_mul_natCast (by norm_num) (-a) n
  have hcb : (3 : ℝ) ^ (-((n : ℤ) : ℝ) * Q * (d : ℝ) / 2) = rb ^ n := by
    rw [show -((n : ℤ) : ℝ) * Q * (d : ℝ) / 2 =
        -(Q * (d : ℝ) / 2) * (n : ℝ) by push_cast; ring]
    exact Real.rpow_mul_natCast (by norm_num) (-(Q * (d : ℝ) / 2)) n
  have hcr : (3 : ℝ) ^ (-((n : ℤ) : ℝ) * rho) = rr ^ n := by
    rw [show -((n : ℤ) : ℝ) * rho = -rho * (n : ℝ) by push_cast; ring]
    exact Real.rpow_mul_natCast (by norm_num) (-rho) n
  refine ⟨(n : ℤ), by exact_mod_cast hn1, ?_, ?_⟩
  dsimp [lambdaPort, lambdaCen]
  change max
      ((3 : ℝ) ^ (-((n : ℤ) : ℝ) * a) +
        A * (3 : ℝ) ^ (-((n : ℤ) : ℝ) * Q * (d : ℝ) / 2))
      ((3 : ℝ) ^ (-((n : ℤ) : ℝ) * a)) ≤ 1 / 4
  · apply max_le
    · rw [hca, hcb]
      have hmul := mul_le_mul_of_nonneg_left hpb hA.le
      have hAe : A * (1 / (8 * A)) = (1 : ℝ) / 8 := by field_simp
      rw [hAe] at hmul
      linarith only [hpa, hmul]
    · rw [hca]
      linarith only [hpa]
  · dsimp [rho] at hcr ⊢
    rw [hcr]
    exact hpr

/-! ## Elementary right-hand choices -/

/-- A continuous real function which is strictly below a target at zero stays
below that target on a positive right-hand interval. -/
theorem exists_right_radius {f : ℝ → ℝ} {A : ℝ}
    (hf : ContinuousAt f 0) (hA : f 0 < A) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 0 ≤ x → x ≤ r → f x ≤ A := by
  have hmem : Set.Iio A ∈ nhds (f 0) := Iio_mem_nhds hA
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hf.preimage_mem_nhds hmem)
  refine ⟨r / 2, by positivity, fun x hx hxr => ?_⟩
  have hdist : dist x 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx]
    linarith only [hxr, hr]
  exact (hball hdist).le

/-- A positive terminal determinant tolerance satisfies the two continuity
conditions and both structural caps printed in Phase 0. -/
theorem exists_deltaTerm (d H : ℕ) {g AH etaNew etaDr etaOut epsCal deltaDetBar : ℝ}
    (hnew : (1 + (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ))) * etaNew < etaDr)
    (hetaOut : 0 < etaOut) (hepsCal : 0 < epsCal) (hdeltaDet : 0 < deltaDetBar) :
    ∃ deltaTerm : ℝ, 0 < deltaTerm ∧ deltaTerm ≤ epsCal ∧
      deltaTerm ≤ deltaDetBar ∧
      AH * (Real.exp ((initExpQ d g : ℝ) * (d : ℝ) *
        Real.log (1 + deltaTerm)) - 1) ≤ etaOut / 4 ∧
      (1 + (1 + deltaTerm) ^ d *
          (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ))) * etaNew +
        2 * (d : ℝ) * ((1 + deltaTerm) ^ d - 1) ≤ etaDr := by
  let F : ℝ → ℝ := fun x => AH *
    (Real.exp ((initExpQ d g : ℝ) * (d : ℝ) * Real.log (1 + x)) - 1)
  let G : ℝ → ℝ := fun x =>
    (1 + (1 + x) ^ d * (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ))) * etaNew +
      2 * (d : ℝ) * ((1 + x) ^ d - 1)
  have hFcont : ContinuousAt F 0 := by
    dsimp [F]
    have hlog : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    have hinner : ContinuousAt
        (fun x : ℝ => (initExpQ d g : ℝ) * (d : ℝ) * Real.log (1 + x)) 0 :=
      continuousAt_const.mul hlog
    have hexp : ContinuousAt
        (fun x : ℝ => Real.exp ((initExpQ d g : ℝ) * (d : ℝ) *
          Real.log (1 + x))) 0 := Real.continuous_exp.continuousAt.comp' hinner
    exact continuousAt_const.mul (hexp.sub continuousAt_const)
  have hGcont : ContinuousAt G 0 := by dsimp [G]; fun_prop
  have hF0 : F 0 < etaOut / 4 := by dsimp [F]; norm_num; linarith only [hetaOut]
  have hG0 : G 0 < etaDr := by simpa [G] using hnew
  obtain ⟨rF, hrF, hF⟩ := exists_right_radius hFcont hF0
  obtain ⟨rG, hrG, hG⟩ := exists_right_radius hGcont hG0
  let deltaTerm : ℝ := min epsCal (min deltaDetBar (min rF rG))
  have hdelta : 0 < deltaTerm := by dsimp [deltaTerm]; positivity
  refine ⟨deltaTerm, hdelta, min_le_left _ _,
    le_trans (min_le_right _ _) (min_le_left _ _), ?_, ?_⟩
  · exact hF deltaTerm hdelta.le
      (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _))
  · exact hG deltaTerm hdelta.le
      (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _))

end

end Selection
end HighContrast
end Homogenization
