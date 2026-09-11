/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Work
import HCPoly.Provider.ShortHop.DeterminantDrift

/-!
# Drift-index estimates for the global selector

The dyadic drift index has a fixed additive load under an arbitrary
same-grid advance.  On a calm service interval it either drops by one or
remains zero, according to its incoming value.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- The additive load in the general drift-index propagation row. -/
def driftIndexLoad (d : ℕ) (etaPre : ℝ) : ℝ :=
  1 + Real.logb 2 (1 + 2 * (d : ℝ) / etaPre)

/-- Defining equation for the drift-index load. -/
theorem driftIndexLoad_eq (d : ℕ) (etaPre : ℝ) :
    driftIndexLoad d etaPre =
      1 + Real.logb 2 (1 + 2 * (d : ℝ) / etaPre) := rfl

private theorem linearDrift_nonneg_of_meanOrder {P : Measure (CoeffSpace d)}
    {rhoDr : ℝ} {q : Mat d} {jStar T v : ℤ} (hjT : jStar ≤ T)
    (hTv : T ≤ v)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v →
      (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v →
      toFullBlockMat (adaptedMean P q t) ≤
        toFullBlockMat (adaptedMean P q s)) :
    0 ≤ linearDrift P rhoDr q jStar T := by
  apply ShortHop.linearDrift_nonneg (hpos T hjT hTv)
  intro r hr hrT
  exact hmono (r - 1) r (by omega) (by omega) (hrT.trans hTv)

private theorem linearDrift_le_exp_mul_add (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} {rhoDr : ℝ} (hrho : 0 ≤ rhoDr)
    {q : Mat d} {jStar u v : ℤ} (hju : jStar ≤ u) (huv : u ≤ v)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v →
      (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v →
      toFullBlockMat (adaptedMean P q t) ≤
        toFullBlockMat (adaptedMean P q s)) :
    linearDrift P rhoDr q jStar v ≤
      Real.exp ((d : ℝ) * detLoss P q u v) *
        (linearDrift P rhoDr q jStar u + 2 * (d : ℝ)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hgap : 0 ≤ (v : ℝ) - (u : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast huv)
  have hdisc :
      (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrho) hgap)
  have hDu : 0 ≤ linearDrift P rhoDr q jStar u :=
    linearDrift_nonneg_of_meanOrder hju huv hpos hmono
  have hprop := ShortHop.linearDrift_propagation_exp (P := P)
    (rhoDr := rhoDr) (q := q) (jStar := jStar) (u := u) (v := v)
    (by omega : d ≠ 0) hrho hju huv hpos hmono
  set E : ℝ := Real.exp ((d : ℝ) * detLoss P q u v)
  set G : ℝ := (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ)))
  set Du : ℝ := linearDrift P rhoDr q jStar u
  set Dv : ℝ := linearDrift P rhoDr q jStar v
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hfirst : E * G * Du ≤ E * Du := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hE hdisc) hDu
  have htwo : 0 ≤ 2 * (d : ℝ) := mul_nonneg (by norm_num) hd0
  change Dv ≤ E * (Du + 2 * (d : ℝ))
  change Dv ≤ E * G * Du + 2 * (d : ℝ) * (E - 1) at hprop
  calc
    Dv ≤ E * G * Du + 2 * (d : ℝ) * (E - 1) := hprop
    _ ≤ E * Du + 2 * (d : ℝ) * (E - 1) :=
      add_le_add hfirst le_rfl
    _ = E * Du + (E * (2 * (d : ℝ)) - 2 * (d : ℝ)) := by ring
    _ ≤ E * Du + E * (2 * (d : ℝ)) :=
      add_le_add le_rfl (sub_le_self (E * (2 * (d : ℝ))) htwo)
    _ = E * (Du + 2 * (d : ℝ)) := by ring

private theorem driftIndex_general_raw (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} {rhoDr etaPre : ℝ}
    (hrho : 0 ≤ rhoDr) (hetaPre : 0 < etaPre)
    {q : Mat d} {jStar u v : ℤ} (hju : jStar ≤ u) (huv : u ≤ v)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v →
      (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v →
      toFullBlockMat (adaptedMean P q t) ≤
        toFullBlockMat (adaptedMean P q s)) :
    (⌈Real.logb 2 (max 1
        (linearDrift P rhoDr q jStar v / etaPre))⌉₊ : ℝ) ≤
      (⌈Real.logb 2 (max 1
        (linearDrift P rhoDr q jStar u / etaPre))⌉₊ : ℝ) +
        driftIndexLoad d etaPre +
          (d : ℝ) / Real.log 2 * detLoss P q u v := by
  have hrootv : 0 < adaptedDetRoot P q v :=
    ShortHop.detRoot_pos (hpos v (hju.trans huv) le_rfl)
  have hroot : adaptedDetRoot P q v ≤ adaptedDetRoot P q u :=
    ShortHop.detRoot_le_of_blockMatLoewnerLE
      (hpos v (hju.trans huv) le_rfl) (hpos u hju huv)
      (hmono u v hju huv le_rfl)
  have hsigma : 0 ≤ detLoss P q u v := by
    rw [detLoss]
    exact sub_nonneg.mpr (Real.log_le_log hrootv hroot)
  have hlinear := linearDrift_le_exp_mul_add hd hrho hju huv hpos hmono
  set E : ℝ := Real.exp ((d : ℝ) * detLoss P q u v)
  set A : ℝ := max 1 (linearDrift P rhoDr q jStar u / etaPre)
  set F : ℝ := 1 + 2 * (d : ℝ) / etaPre
  set V : ℝ := max 1 (linearDrift P rhoDr q jStar v / etaPre)
  have hE1 : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (Nat.cast_nonneg d) hsigma)
  have hA1 : 1 ≤ A := by dsimp [A]; exact le_max_left _ _
  have hF1 : 1 ≤ F := by
    dsimp [F]
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hetaPre.le)
  have hDuA : linearDrift P rhoDr q jStar u / etaPre ≤ A := by
    dsimp [A]
    exact le_max_right _ _
  have hdim : 0 ≤ 2 * (d : ℝ) / etaPre :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hetaPre.le
  have hdimA : 2 * (d : ℝ) / etaPre ≤ A * (2 * (d : ℝ) / etaPre) := by
    calc
      2 * (d : ℝ) / etaPre = 1 * (2 * (d : ℝ) / etaPre) := by ring
      _ ≤ A * (2 * (d : ℝ) / etaPre) :=
        mul_le_mul_of_nonneg_right hA1 hdim
  have hsum :
      (linearDrift P rhoDr q jStar u + 2 * (d : ℝ)) / etaPre ≤ A * F := by
    rw [add_div, mul_add]
    simpa only [mul_one] using add_le_add hDuA hdimA
  have hratio :
      linearDrift P rhoDr q jStar v / etaPre ≤ E * A * F := by
    calc
      linearDrift P rhoDr q jStar v / etaPre ≤
          (E * (linearDrift P rhoDr q jStar u + 2 * (d : ℝ))) / etaPre :=
        (div_le_div_iff_of_pos_right hetaPre).mpr hlinear
      _ = E * ((linearDrift P rhoDr q jStar u + 2 * (d : ℝ)) / etaPre) := by
        ring
      _ ≤ E * (A * F) :=
        mul_le_mul_of_nonneg_left hsum (zero_le_one.trans hE1)
      _ = E * A * F := by ring
  have hprod1 : 1 ≤ E * A * F := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hE1 hA1) hF1
  have hV : V ≤ E * A * F := by
    dsimp [V]
    exact max_le hprod1 hratio
  have hV0 : 0 < V := lt_of_lt_of_le zero_lt_one (by dsimp [V]; exact le_max_left _ _)
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE1
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hF0 : 0 < F := lt_of_lt_of_le zero_lt_one hF1
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hV0 hV
  have hlogE : Real.logb 2 E =
      (d : ℝ) / Real.log 2 * detLoss P q u v := by
    dsimp [E, Real.logb]
    rw [Real.log_exp]
    ring
  rw [Real.logb_mul (mul_ne_zero hE0.ne' hA0.ne') hF0.ne',
    Real.logb_mul hE0.ne' hA0.ne', hlogE] at hlog
  have hlogV0 : 0 ≤ Real.logb 2 V :=
    Real.logb_nonneg (by norm_num) (by dsimp [V]; exact le_max_left _ _)
  have hceilV : (⌈Real.logb 2 V⌉₊ : ℝ) ≤ Real.logb 2 V + 1 :=
    (Nat.ceil_lt_add_one hlogV0).le
  have hceilA : Real.logb 2 A ≤ (⌈Real.logb 2 A⌉₊ : ℝ) :=
    Nat.le_ceil _
  change (⌈Real.logb 2 V⌉₊ : ℝ) ≤
    (⌈Real.logb 2 A⌉₊ : ℝ) + driftIndexLoad d etaPre +
      (d : ℝ) / Real.log 2 * detLoss P q u v
  rw [driftIndexLoad_eq]
  linarith only [hceilV, hlog, hceilA]

/-- The general drift-index row for a same-grid cursor advance. -/
theorem driftIndex_general (hd : 2 ≤ d) {P : Measure (CoeffSpace d)}
    {rhoDr etaPre : ℝ} (hrho : 0 ≤ rhoDr) (hetaPre : 0 < etaPre)
    {jStar v : ℤ} (S : State d) (hju : jStar ≤ S.cursor)
    (huv : S.cursor ≤ v)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v →
      (toFullBlockMat (adaptedMean P S.q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v →
      toFullBlockMat (adaptedMean P S.q t) ≤
        toFullBlockMat (adaptedMean P S.q s)) :
    (driftIndex P rhoDr etaPre jStar {S with cursor := v} : ℝ) ≤
      (driftIndex P rhoDr etaPre jStar S : ℝ) + driftIndexLoad d etaPre +
        (d : ℝ) / Real.log 2 * detLoss P S.q S.cursor v := by
  change (⌈Real.logb 2 (max 1
      (linearDrift P rhoDr S.q jStar v / etaPre))⌉₊ : ℝ) ≤ _
  exact driftIndex_general_raw hd hrho hetaPre hju huv hpos hmono

private theorem linearDrift_calm (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} {rhoDr etaPre rDr : ℝ}
    (hrho : 0 ≤ rhoDr) {q : Mat d}
    {jStar u h : ℤ} (hju : jStar ≤ u) (hh : 1 ≤ h)
    (hservice : (3 : ℝ) ^ (-(h : ℝ) * rhoDr) ≤ 1 / 8)
    (hratio : adaptedDetRoot P q u / adaptedDetRoot P q (u + h) ≤ rDr)
    (hrpow : rDr ^ d ≤ 2)
    (hrdrift : 2 * (d : ℝ) * (rDr ^ d - 1) ≤ etaPre / 4)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ u + h →
      (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ u + h →
      toFullBlockMat (adaptedMean P q t) ≤
        toFullBlockMat (adaptedMean P q s)) :
    linearDrift P rhoDr q jStar (u + h) ≤
      (1 / 4) * linearDrift P rhoDr q jStar u + etaPre / 4 := by
  have huv : u ≤ u + h := by omega
  have huPos := hpos u hju huv
  have hvPos := hpos (u + h) (hju.trans huv) le_rfl
  have hrootu : 0 < adaptedDetRoot P q u := ShortHop.detRoot_pos huPos
  have hrootv : 0 < adaptedDetRoot P q (u + h) := ShortHop.detRoot_pos hvPos
  have hratio0 : 0 ≤ adaptedDetRoot P q u / adaptedDetRoot P q (u + h) :=
    (div_pos hrootu hrootv).le
  have hratioPow :
      (adaptedDetRoot P q u / adaptedDetRoot P q (u + h)) ^ d ≤ rDr ^ d :=
    pow_le_pow_left₀ hratio0 hratio d
  have hdetRoot := ShortHop.detRoot_div_pow (d := d) (by omega : d ≠ 0) huPos hvPos
  have hprop := ShortHop.linearDrift_propagation (P := P) (rhoDr := rhoDr)
    (q := q) (jStar := jStar) (u := u) (v := u + h)
    hrho hju huv hpos hmono
  rw [← hdetRoot] at hprop
  have hgap : -rhoDr * (((u + h : ℤ) : ℝ) - (u : ℝ)) =
      -(h : ℝ) * rhoDr := by
    push_cast
    ring
  rw [hgap] at hprop
  have hdisc0 : 0 ≤ (3 : ℝ) ^ (-(h : ℝ) * rhoDr) := by positivity
  have hcoef :
      (adaptedDetRoot P q u / adaptedDetRoot P q (u + h)) ^ d *
          (3 : ℝ) ^ (-(h : ℝ) * rhoDr) ≤ 1 / 4 := by
    calc
      _ ≤ 2 * (1 / 8) :=
        mul_le_mul (hratioPow.trans hrpow) hservice hdisc0 (by norm_num)
      _ = 1 / 4 := by norm_num
  have hadd :
      2 * (d : ℝ) *
          ((adaptedDetRoot P q u / adaptedDetRoot P q (u + h)) ^ d - 1) ≤
        etaPre / 4 := by
    exact (mul_le_mul_of_nonneg_left
      (sub_le_sub_right hratioPow 1)
      (mul_nonneg (by norm_num) (Nat.cast_nonneg d))).trans hrdrift
  have hDu : 0 ≤ linearDrift P rhoDr q jStar u :=
    linearDrift_nonneg_of_meanOrder hju huv hpos hmono
  exact hprop.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcoef hDu) hadd)

private theorem natCeil_logb_calm {D D' eta : ℝ} (heta : 0 < eta)
    (hcalm : D' ≤ (1 / 4) * D + eta / 4) :
    (0 < ⌈Real.logb 2 (max 1 (D / eta))⌉₊ →
      ⌈Real.logb 2 (max 1 (D' / eta))⌉₊ ≤
        ⌈Real.logb 2 (max 1 (D / eta))⌉₊ - 1) ∧
      (⌈Real.logb 2 (max 1 (D / eta))⌉₊ = 0 →
        ⌈Real.logb 2 (max 1 (D' / eta))⌉₊ = 0) := by
  have hUpos : 0 < max 1 (D / eta) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hVpos : 0 < max 1 (D' / eta) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcalmDiv : D' / eta ≤ (1 / 4) * (D / eta) + 1 / 4 := by
    calc
      D' / eta ≤ ((1 / 4) * D + eta / 4) / eta :=
        (div_le_div_iff_of_pos_right heta).mpr hcalm
      _ = (1 / 4) * (D / eta) + 1 / 4 := by field_simp
  constructor
  · intro hb
    let b : ℕ := ⌈Real.logb 2 (max 1 (D / eta))⌉₊
    change 0 < b at hb
    change ⌈Real.logb 2 (max 1 (D' / eta))⌉₊ ≤ b - 1
    have hlogU : Real.logb 2 (max 1 (D / eta)) ≤ (b : ℝ) := by
      exact Nat.le_ceil _
    have hmaxU : max 1 (D / eta) ≤ (2 : ℝ) ^ b := by
      have hpow := (Real.logb_le_iff_le_rpow (by norm_num) hUpos).mp hlogU
      simpa only [Real.rpow_natCast] using hpow
    have hDU : D / eta ≤ (2 : ℝ) ^ b :=
      (le_max_right _ _).trans hmaxU
    have hDV : D' / eta ≤ (1 / 4) * (2 : ℝ) ^ b + 1 / 4 :=
      hcalmDiv.trans (add_le_add
        (mul_le_mul_of_nonneg_left hDU (by norm_num : (0 : ℝ) ≤ 1 / 4)) le_rfl)
    obtain ⟨n, hbn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
    rw [hbn] at hDV ⊢
    have hpowOne : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hquarter :
        (1 / 4) * (2 : ℝ) ^ n.succ + 1 / 4 ≤ (2 : ℝ) ^ n := by
      rw [pow_succ]
      nlinarith only [hpowOne]
    apply Nat.ceil_le.mpr
    rw [Real.logb_le_iff_le_rpow (by norm_num) hVpos,
      Real.rpow_natCast]
    simpa only [Nat.succ_sub_one] using max_le hpowOne (hDV.trans hquarter)
  · intro hb
    have hlogU : Real.logb 2 (max 1 (D / eta)) ≤ 0 :=
      Nat.ceil_eq_zero.mp hb
    have hmaxU : max 1 (D / eta) ≤ 1 := by
      have hpow := (Real.logb_le_iff_le_rpow (by norm_num) hUpos).mp hlogU
      simpa only [Real.rpow_zero] using hpow
    have hDU : D / eta ≤ 1 := (le_max_right _ _).trans hmaxU
    have hDV : D' / eta ≤ 1 := by
      calc
        D' / eta ≤ (1 / 4) * (D / eta) + 1 / 4 := hcalmDiv
        _ ≤ 1 := by linarith only [hDU]
    apply Nat.ceil_eq_zero.mpr
    rw [Real.logb_le_iff_le_rpow (by norm_num) hVpos, Real.rpow_zero]
    exact max_le le_rfl hDV

/-- On a calm service interval, a positive drift index drops by one and a
zero drift index remains zero. -/
theorem driftIndex_calm (hd : 2 ≤ d) {P : Measure (CoeffSpace d)}
    {rhoDr etaPre rDr : ℝ} (hrho : 0 ≤ rhoDr) (hetaPre : 0 < etaPre)
    {jStar h : ℤ} (S : State d) (hju : jStar ≤ S.cursor) (hh : 1 ≤ h)
    (hservice : (3 : ℝ) ^ (-(h : ℝ) * rhoDr) ≤ 1 / 8)
    (hratio : adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + h) ≤ rDr)
    (hrpow : rDr ^ d ≤ 2)
    (hrdrift : 2 * (d : ℝ) * (rDr ^ d - 1) ≤ etaPre / 4)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ S.cursor + h →
      (toFullBlockMat (adaptedMean P S.q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ S.cursor + h →
      toFullBlockMat (adaptedMean P S.q t) ≤
        toFullBlockMat (adaptedMean P S.q s)) :
    (0 < driftIndex P rhoDr etaPre jStar S →
      driftIndex P rhoDr etaPre jStar {S with cursor := S.cursor + h} ≤
        driftIndex P rhoDr etaPre jStar S - 1) ∧
      (driftIndex P rhoDr etaPre jStar S = 0 →
        driftIndex P rhoDr etaPre jStar {S with cursor := S.cursor + h} = 0) := by
  have huv : S.cursor ≤ S.cursor + h := by omega
  have hcalm := linearDrift_calm hd hrho hju hh hservice hratio
    hrpow hrdrift hpos hmono
  change (0 < ⌈Real.logb 2 (max 1
      (linearDrift P rhoDr S.q jStar S.cursor / etaPre))⌉₊ → _) ∧ _
  exact natCeil_logb_calm hetaPre hcalm

end

end Selection
end HighContrast
end Homogenization
