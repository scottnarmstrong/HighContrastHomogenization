/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.DriftWork
import HCPoly.Provider.Selection.Transitions
/-!
# Progress weights and the one-step potential estimate

The progress weights are chosen after the branch loads are known.  Their
ordered inequalities turn each analytic branch row into the same potential
drop, with the additional hop debit on a grid change.
-/
namespace Homogenization.HighContrast.Selection
noncomputable section
variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
variable {C1 C4 C5 C6 Cslope : ℝ}
/-- The strict profile-work decrement used in the progress margin. -/
def potentialWorkDecrement (c : Constants d H g epsCal etaDr etaProfBar
    deltaDetBar Cd Khop Ctr Ltr) : ℝ :=
  workDecrement (lambdaPort d (initExpQ d g : ℝ) (initExpA g) c.Crec c.h)

/-- Defining equation for the profile-work decrement. -/
theorem potentialWorkDecrement_eq :
    potentialWorkDecrement c =
      workDecrement (lambdaPort d (initExpQ d g : ℝ) (initExpA g) c.Crec c.h) := rfl
/-- The largest fixed additive load among the non-hop branches. -/
def potentialLoad (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar
    Cd Khop Ctr Ltr) (C1 C4 C6 : ℝ) : ℝ :=
  max C1 (max C4 (max C6 (driftIndexLoad d c.etaPre)))

/-- The least determinant-charge scale available in a costly branch. -/
def potentialScale (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar
    Cd Khop Ctr Ltr) : ℝ :=
  min (Real.log c.rDr)
    (min (Real.log (1 + c.deltaShort)) (Real.log (1 + c.deltaTerm)))

/-- Defining equation for the least determinant-charge scale. -/
theorem potentialScale_eq :
    potentialScale c = min (Real.log c.rDr)
      (min (Real.log (1 + c.deltaShort)) (Real.log (1 + c.deltaTerm))) := rfl

/-- The unweighted determinant feedback charged by one projective hop. -/
def hopFeedback (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar
    Cd Khop Ctr Ltr) : ℝ :=
  2 * c.CdetBar * ((c.h : ℝ) + 2) * Real.log (1 + c.etaX)

/-- Defining equation for the projective-hop feedback. -/
theorem hopFeedback_eq :
    hopFeedback c =
      2 * c.CdetBar * ((c.h : ℝ) + 2) * Real.log (1 + c.etaX) := rfl

/-- The least determinant-charge scale is strictly positive. -/
theorem potentialScale_pos : 0 < potentialScale c := by
  rw [potentialScale_eq]
  exact lt_min (Real.log_pos c.one_lt_rDr)
    (lt_min (Real.log_pos (by linarith only [c.deltaShort_pos]))
      (Real.log_pos (by linarith only [c.deltaTerm_pos])))

/-- The ordered weights used by the selector potential. -/
structure ProgressWeights
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr)
    (C1 C4 C5 C6 Cslope : ℝ) where
  c0 : ℝ
  Gfresh : ℝ
  alphaW : ℝ
  alphaX : ℝ
  alphaSearch : ℝ
  alphaFresh : ℝ
  Cdet : ℝ
  mHop : ℝ
  C1_nonneg : 0 ≤ C1
  C4_nonneg : 0 ≤ C4
  C5_nonneg : 0 ≤ C5
  C6_nonneg : 0 ≤ C6
  Cslope_nonneg : 0 ≤ Cslope
  c0_pos : 0 < c0
  c0_lt_half : c0 < 1 / 2 * min 1 (c.etaReady * potentialWorkDecrement c)
  Gfresh_pos : 0 < Gfresh
  fresh_margin : C1 + c0 < Gfresh
  two_le_alphaX : 2 ≤ alphaX
  projective_weight :
    C5 + Gfresh + c0 + alphaX * hopFeedback c ≤
      alphaX * (c.chop - projectiveError c.etaX)
  determinant_weight :
    4 * (potentialLoad c C1 C4 C6 + C5 + Gfresh + 2 * c0) ≤
      alphaX * c.CdetBar * potentialScale c
  slope_weight : 4 * Cslope ≤ alphaX * c.CdetBar
  alphaW_eq : alphaW = c.etaReady
  alphaW_pos : 0 < alphaW
  alphaSearch_eq : alphaSearch =
    C5 + alphaX * projectiveError c.etaX + c0 + alphaX * hopFeedback c
  alphaFresh_eq : alphaFresh = alphaSearch + Gfresh
  Cdet_eq : Cdet = determinantCoefficient c.CdetBar alphaX
  mHop_eq : mHop = 2 * Cdet * ((c.h : ℝ) + 2) * Real.log (1 + c.etaX)

private theorem projectiveError_nonneg : 0 ≤ projectiveError c.etaX := by
  rw [projectiveError_eq]
  have hden : 0 < 1 - c.etaX := by linarith only [c.etaX_le_quarter]
  have hratio : 1 ≤ (1 + c.etaX) / (1 - c.etaX) := by
    rw [le_div_iff₀ hden]
    linarith only [c.etaX_pos]
  exact mul_nonneg (by norm_num) (Real.log_nonneg hratio)

private theorem hopFeedback_nonneg : 0 ≤ hopFeedback c := by
  rw [hopFeedback_eq]
  have hh : 0 < (c.h : ℝ) + 2 := by
    have : (1 : ℝ) ≤ c.h := by exact_mod_cast c.one_le_h
    linarith only [this]
  have hlog : 0 < Real.log (1 + c.etaX) :=
    Real.log_pos (by linarith only [c.etaX_pos])
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) c.CdetBar_pos.le) hh.le) hlog.le

/-- The source-ordered progress weights exist for nonnegative branch loads. -/
theorem exists_progressWeights (hC1 : 0 ≤ C1) (hC4 : 0 ≤ C4)
    (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hCslope : 0 ≤ Cslope) :
    Nonempty (ProgressWeights c C1 C4 C5 C6 Cslope) := by
  have hlam0 : 0 ≤ lambdaPort d (initExpQ d g : ℝ) (initExpA g) c.Crec c.h :=
    (Real.rpow_nonneg (by norm_num) _).trans (le_max_right _ _)
  have hwork : 0 < potentialWorkDecrement c := by
    rw [potentialWorkDecrement_eq]
    exact workDecrement_pos hlam0 (c.service_le.trans_lt (by norm_num))
  have hreadyWork : 0 < c.etaReady * potentialWorkDecrement c :=
    mul_pos c.etaReady_pos hwork
  let c0 : ℝ := min 1 (c.etaReady * potentialWorkDecrement c) / 4
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hc0half : c0 < 1 / 2 * min 1 (c.etaReady * potentialWorkDecrement c) := by
    dsimp [c0]
    have hmin : 0 < min 1 (c.etaReady * potentialWorkDecrement c) :=
      lt_min one_pos hreadyWork
    linarith only [hmin]
  let Gfresh : ℝ := C1 + c0 + 1
  have hGfresh : 0 < Gfresh := by dsimp [Gfresh]; linarith only [hC1, hc0]
  have hmargin : C1 + c0 < Gfresh := by
    dsimp [Gfresh]
    exact lt_add_of_pos_right _ one_pos
  have hscale := potentialScale_pos (c := c)
  have hmu := hopFeedback_nonneg (c := c)
  have heps : projectiveError c.etaX ≤ c.chop / 4 := by
    simpa only [projectiveError_eq] using c.projective_tolerance
  have hhop : hopFeedback c ≤ c.chop / 4 := by
    rw [hopFeedback_eq]
    exact c.bridge_feedback.trans
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  let gap : ℝ := c.chop - projectiveError c.etaX - hopFeedback c
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith only [c.chop_pos, heps, hhop]
  let detScale : ℝ := c.CdetBar * potentialScale c
  have hdetScale : 0 < detScale := by
    dsimp [detScale]
    exact mul_pos c.CdetBar_pos hscale
  let alphaX : ℝ := max 2 (max ((C5 + Gfresh + c0) / gap)
    (max (4 * (potentialLoad c C1 C4 C6 + C5 + Gfresh + 2 * c0) / detScale)
      (4 * Cslope / c.CdetBar)))
  have halpha : 2 ≤ alphaX := le_max_left _ _
  have hprojRatio : (C5 + Gfresh + c0) / gap ≤ alphaX :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hloadRatio :
      4 * (potentialLoad c C1 C4 C6 + C5 + Gfresh + 2 * c0) / detScale ≤
        alphaX :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hslopeRatio : 4 * Cslope / c.CdetBar ≤ alphaX :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hprojective := (div_le_iff₀ hgap).mp hprojRatio
  have hdeterminant := (div_le_iff₀ hdetScale).mp hloadRatio
  have hslope := (div_le_iff₀ c.CdetBar_pos).mp hslopeRatio
  let alphaSearch := C5 + alphaX * projectiveError c.etaX + c0 +
    alphaX * hopFeedback c
  let alphaFresh := alphaSearch + Gfresh
  let Cdet := determinantCoefficient c.CdetBar alphaX
  let mHop := 2 * Cdet * ((c.h : ℝ) + 2) * Real.log (1 + c.etaX)
  refine ⟨⟨c0, Gfresh, c.etaReady, alphaX, alphaSearch, alphaFresh, Cdet, mHop,
    hC1, hC4, hC5, hC6, hCslope, hc0, hc0half, hGfresh, hmargin, halpha,
    ?_, ?_, ?_, rfl, c.etaReady_pos, rfl, rfl, rfl, rfl⟩⟩
  · calc
      C5 + Gfresh + c0 + alphaX * hopFeedback c ≤
          alphaX * gap + alphaX * hopFeedback c := add_le_add hprojective le_rfl
      _ = alphaX * (c.chop - projectiveError c.etaX) := by
        dsimp [gap]
        ring
  · simpa only [detScale, mul_assoc] using hdeterminant
  · simpa only [mul_comm] using hslope

/-- The determinant weight is the chosen projective weight times its
dimension-only coefficient. -/
theorem ProgressWeights.Cdet_eq_mul (w : ProgressWeights c C1 C4 C5 C6 Cslope) :
    w.Cdet = c.CdetBar * w.alphaX := by
  rw [w.Cdet_eq, determinantCoefficient_eq]

/-- The determinant weight is positive. -/
theorem ProgressWeights.Cdet_pos (w : ProgressWeights c C1 C4 C5 C6 Cslope) :
    0 < w.Cdet := by
  rw [w.Cdet_eq_mul]
  exact mul_pos c.CdetBar_pos (lt_of_lt_of_le (by norm_num) w.two_le_alphaX)
theorem ProgressWeights.alphaX_nonneg
    (w : ProgressWeights c C1 C4 C5 C6 Cslope) : 0 ≤ w.alphaX :=
  le_trans (by norm_num) w.two_le_alphaX

/-- The hop debit is the projective weight times the unweighted feedback. -/
theorem ProgressWeights.mHop_eq_alphaX_mul
    (w : ProgressWeights c C1 C4 C5 C6 Cslope) :
    w.mHop = w.alphaX * hopFeedback c := by
  rw [w.mHop_eq, w.Cdet_eq_mul, hopFeedback_eq]
  ring

/-- The search and fresh phase charges are positive. -/
theorem ProgressWeights.alphaSearch_pos
    (w : ProgressWeights c C1 C4 C5 C6 Cslope) : 0 < w.alphaSearch := by
  rw [w.alphaSearch_eq]
  have heps := projectiveError_nonneg (c := c)
  have hmu := hopFeedback_nonneg (c := c)
  have ha : 0 ≤ w.alphaX := le_trans (by norm_num) w.two_le_alphaX
  have hleft : 0 ≤ C5 + w.alphaX * projectiveError c.etaX :=
    add_nonneg w.C5_nonneg (mul_nonneg ha heps)
  exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hleft w.c0_pos)
    (mul_nonneg ha hmu)

theorem ProgressWeights.alphaFresh_pos
    (w : ProgressWeights c C1 C4 C5 C6 Cslope) : 0 < w.alphaFresh := by
  rw [w.alphaFresh_eq]
  exact add_pos w.alphaSearch_pos w.Gfresh_pos

/-- The scalar rows supplied by the analytic branch estimates. -/
inductive PotentialRow (w : ProgressWeights c C1 C4 C5 C6 Cslope) :
    TransitionRule → ℝ → ℝ → Prop where
  | t1 {ΔF dτ : ℝ} (hΔ : ΔF ≤ C1 - w.Gfresh + Cslope * dτ) : PotentialRow w .t1 ΔF dτ
  | t2Calm {ΔF dτ : ℝ} (hΔ : ΔF ≤ -1 + c.Cdir * w.alphaX * dτ) : PotentialRow w .t2 ΔF dτ
  | t3Calm {ΔF dτ : ℝ} (hΔ : ΔF ≤ -w.alphaW * potentialWorkDecrement c +
      c.Cdir * w.alphaX * dτ) : PotentialRow w .t3 ΔF dτ
  | t2Noncalm {ΔF dτ : ℝ} (hscale : potentialScale c < dτ)
      (hΔ : ΔF ≤ potentialLoad c C1 C4 C6 + c.Cdir * w.alphaX * dτ) :
      PotentialRow w .t2 ΔF dτ
  | t3Noncalm {ΔF dτ : ℝ} (hscale : potentialScale c < dτ)
      (hΔ : ΔF ≤ potentialLoad c C1 C4 C6 + c.Cdir * w.alphaX * dτ) :
      PotentialRow w .t3 ΔF dτ
  | t4 {ΔF dτ : ℝ} (hscale : potentialScale c < dτ)
      (hΔ : ΔF ≤ potentialLoad c C1 C4 C6 + c.Cdir * w.alphaX * dτ) :
      PotentialRow w .t4 ΔF dτ
  | t5Nonfinal {ΔF dτ : ℝ} (hΔ : ΔF ≤ C5 + w.Gfresh -
      w.alphaX * (c.chop - projectiveError c.etaX) + w.Cdet / 4 * dτ) :
      PotentialRow w .t5 ΔF dτ
  | t5Final {ΔF dτ : ℝ} (hΔ : ΔF ≤ C5 + w.alphaX * projectiveError c.etaX -
      w.alphaSearch) : PotentialRow w .t5 ΔF dτ
  | t6 {ΔF dτ : ℝ} (hterm : Real.log (1 + c.deltaTerm) ≤ dτ)
      (hΔ : ΔF ≤ potentialLoad c C1 C4 C6 + C5 + w.c0 +
        w.alphaX * (projectiveError c.etaX + hopFeedback c) +
          c.Cdir * w.alphaX * dτ) : PotentialRow w .t6 ΔF dτ

/-- Every nonterminal branch row has the common potential drop, including the
exact additional debit on a projective hop. -/
theorem PotentialRow.oneStepPotential
    (w : ProgressWeights c C1 C4 C5 C6 Cslope) {rule : TransitionRule}
    {ΔF dτ : ℝ} (hcharge : 0 ≤ dτ) (hrow : PotentialRow w rule ΔF dτ) :
    ΔF ≤ -w.c0 - w.mHop * (if rule = .t5 then 1 else 0) + w.Cdet * dτ := by
  have ha : 0 ≤ w.alphaX := le_trans (by norm_num) w.two_le_alphaX
  have hCdet : 0 ≤ w.Cdet := w.Cdet_pos.le
  have hbarDir : 4 * c.Cdir ≤ c.CdetBar :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans c.CdetBar_lower
  have hdir : c.Cdir * w.alphaX ≤ w.Cdet / 4 := by
    rw [w.Cdet_eq_mul]
    have := mul_le_mul_of_nonneg_right hbarDir ha
    linarith only [this]
  have hslope : Cslope ≤ w.Cdet / 4 := by
    rw [w.Cdet_eq_mul]
    linarith only [w.slope_weight]
  have hdirτ := mul_le_mul_of_nonneg_right hdir hcharge
  have hslopeτ := mul_le_mul_of_nonneg_right hslope hcharge
  have hquarter : w.Cdet / 4 * dτ ≤ w.Cdet * dτ := by
    apply mul_le_mul_of_nonneg_right _ hcharge
    linarith only [hCdet]
  have hdetWeight :
      4 * (potentialLoad c C1 C4 C6 + C5 + w.Gfresh + 2 * w.c0) ≤
        w.Cdet * potentialScale c := by
    calc
      _ ≤ w.alphaX * c.CdetBar * potentialScale c := w.determinant_weight
      _ = w.Cdet * potentialScale c := by rw [w.Cdet_eq_mul]; ring
  have hloadPaid : ∀ {x : ℝ}, potentialScale c ≤ x →
      potentialLoad c C1 C4 C6 + w.c0 ≤ w.Cdet / 4 * x := by
    intro x hx
    have hmul := mul_le_mul_of_nonneg_left hx hCdet
    have hsmall : potentialLoad c C1 C4 C6 + w.c0 ≤
        potentialLoad c C1 C4 C6 + C5 + w.Gfresh + 2 * w.c0 := by
      linarith only [w.C5_nonneg, w.Gfresh_pos, w.c0_pos]
    linarith only [hdetWeight, hmul, hsmall]
  have hterminalLoad : ∀ {x : ℝ}, potentialScale c ≤ x →
      potentialLoad c C1 C4 C6 + C5 + w.c0 ≤
        -w.c0 + w.Cdet / 4 * x := by
    intro x hx
    have hmul := mul_le_mul_of_nonneg_left hx hCdet
    linarith only [hdetWeight, hmul, w.Gfresh_pos]
  have hc0one : w.c0 < 1 := by
    have hmin := min_le_left (1 : ℝ) (c.etaReady * potentialWorkDecrement c)
    linarith only [w.c0_lt_half, hmin]
  have hc0work : w.c0 < c.etaReady * potentialWorkDecrement c := by
    have hwork : 0 < potentialWorkDecrement c := by
      rw [potentialWorkDecrement_eq]
      exact workDecrement_pos
        ((Real.rpow_nonneg (by norm_num) _).trans (le_max_right _ _))
        (c.service_le.trans_lt (by norm_num))
    have hp := mul_pos c.etaReady_pos hwork
    have hmin := min_le_right (1 : ℝ) (c.etaReady * potentialWorkDecrement c)
    linarith only [w.c0_lt_half, hmin, hp]
  cases hrow with
  | t1 hΔ =>
      simp
      linarith only [hΔ, w.fresh_margin, hslopeτ, hquarter]
  | t2Calm hΔ =>
      simp
      linarith only [hΔ, hc0one, hdirτ, hquarter]
  | t3Calm hΔ =>
      simp
      rw [w.alphaW_eq] at hΔ
      linarith only [hΔ, hc0work, hdirτ, hquarter]
  | t2Noncalm hscale hΔ | t3Noncalm hscale hΔ | t4 hscale hΔ =>
      simp
      have hload := hloadPaid hscale.le
      linarith only [hΔ, hload, hdirτ, hquarter]
  | t5Nonfinal hΔ =>
      simp
      have hm := w.mHop_eq_alphaX_mul
      linarith only [hΔ, w.projective_weight, hm, hquarter]
  | t5Final hΔ =>
      simp
      have hm := w.mHop_eq_alphaX_mul
      have hcharge' : 0 ≤ w.Cdet * dτ := mul_nonneg hCdet hcharge
      linarith only [hΔ, w.alphaSearch_eq, hm, hcharge']
  | t6 hterm hΔ =>
      simp
      have hscale : potentialScale c ≤ dτ :=
        (min_le_right _ _).trans ((min_le_right _ _).trans hterm)
      have hload := hterminalLoad hscale
      have hfeedback : w.alphaX * (projectiveError c.etaX + hopFeedback c) ≤
          w.Cdet / 2 * dτ := by
        have hraw : projectiveError c.etaX + hopFeedback c ≤
            c.CdetBar * Real.log (1 + c.deltaTerm) / 2 := by
          simpa only [projectiveError_eq, hopFeedback_eq] using c.terminal_feedback
        have hmul := mul_le_mul_of_nonneg_left hraw ha
        have htermMul := mul_le_mul_of_nonneg_left hterm (div_nonneg hCdet (by norm_num : (0 : ℝ) ≤ 2))
        calc
          _ ≤ w.alphaX * (c.CdetBar * Real.log (1 + c.deltaTerm) / 2) := hmul
          _ = w.Cdet / 2 * Real.log (1 + c.deltaTerm) := by rw [w.Cdet_eq_mul]; ring
          _ ≤ _ := htermMul
      linarith only [hΔ, hload, hfeedback, hdirτ]
end

end Homogenization.HighContrast.Selection
