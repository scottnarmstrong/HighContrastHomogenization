/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.CappedRun

/-!
# Bounds inherited by the capped selector trace

The trace contains at most its fuel in nonterminal transitions.  Its largest
read scale is bounded by one execution span for the initial decision and one
more for each performed transition, and every visited state retains the
rounded-grid relation.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The integer and real forms of the execution span agree. -/
theorem transitionSpan_cast (h : ℤ) (l0 H : ℕ) :
    (transitionSpan h l0 H : ℝ) = executionSpan h l0 H := by
  simp [transitionSpan, executionSpan]

/-- A terminal selector step reads exactly through the returned terminal
state's upper scale. -/
theorem selectorStep_terminal_readScale_eq
    {P : Measure (CoeffSpace d)} {Q a rhoMax rhoDr : ℝ} {jStar h : ℤ}
    {chop : ℝ} {l0 H : ℕ} {etaReady etaPre deltaShort deltaTerm : ℝ}
    {S T : State d}
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm S).outcome = StepOutcome.terminal T) :
    T.base + (H : ℤ) =
      (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm S).readScale := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;>
    simp [selectorStep, hrule] at hout
  subst T
  simp [selectorStep, hrule]

/-- The upper scale of a terminal outcome is bounded by the largest scale read
by its capped execution. -/
theorem runCapped_terminal_scale_le_queryScale
    {P : Measure (CoeffSpace d)} {Q a rhoMax rhoDr : ℝ} {jStar h : ℤ}
    {chop : ℝ} {l0 H fuel : ℕ} {etaReady etaPre deltaShort deltaTerm : ℝ}
    {S T : State d}
    (hterminal : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm fuel S).outcome = RunOutcome.terminal T) :
    T.base + (H : ℤ) ≤
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).queryScale := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next S' => simp [runCapped, hout] at hterminal
      | terminal state =>
          simp [runCapped, hout] at hterminal
          subst T
          rw [selectorStep_terminal_readScale_eq hout]
          simp [runCapped, hout]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          simp [runCapped, hout] at hterminal
          subst T
          rw [selectorStep_terminal_readScale_eq hout]
          simp [runCapped, hout]
      | next S' =>
          simp only [runCapped, hout] at hterminal ⊢
          exact (ih hterminal).trans (le_max_right _ _)

/-- The largest queried scale is at most one span for each available
transition and one final read. -/
theorem runCapped_queryScale_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d)
    (hh : 0 ≤ h) (hbase : S.base ≤ S.cursor) :
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).queryScale ≤
        S.cursor + ((fuel + 1 : ℕ) : ℤ) * transitionSpan h l0 H := by
  have hspan : 0 ≤ transitionSpan h l0 H := transitionSpan_nonneg hh l0 H
  induction fuel generalizing S with
  | zero =>
      have hread := selectorStep_readScale_le P Q a rhoMax rhoDr jStar h chop
        l0 H etaReady etaPre deltaShort deltaTerm S hbase
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;>
        simpa [runCapped, hout] using hread
  | succ fuel ih =>
      have hread := selectorStep_readScale_le P Q a rhoMax rhoDr jStar h chop
        l0 H etaReady etaPre deltaShort deltaTerm S hbase
      have hstepSpan :
          (((fuel + 1 + 1 : ℕ) : ℤ) * transitionSpan h l0 H) =
            transitionSpan h l0 H +
              (((fuel + 1 : ℕ) : ℤ) * transitionSpan h l0 H) := by
        push_cast
        ring
      have htailSpan :
          0 ≤ (((fuel + 1 : ℕ) : ℤ) * transitionSpan h l0 H) :=
        mul_nonneg (by omega) hspan
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal result =>
          simp only [runCapped, hout]
          rw [hstepSpan]
          omega
      | next S' =>
          have hcursor := selectorStep_next_cursor_le P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S S' hbase hout
          have hbase' := selectorStep_next_base_le_cursor P Q a rhoMax rhoDr jStar
            h chop l0 H etaReady etaPre deltaShort deltaTerm S S' hh hbase hout
          have htail := ih S' hbase'
          simp only [runCapped, hout]
          rw [hstepSpan]
          apply max_le
          · omega
          · omega

/-- Real-valued form of the query bound used by the enclosure arithmetic. -/
theorem runCapped_queryScale_real_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h r0 : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d)
    (hh : 0 ≤ h) (hbase : S.base ≤ S.cursor) (hcursor : S.cursor = r0) :
    ((runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).queryScale : ℝ) ≤
        (r0 : ℝ) + executionSpan h l0 H * (((fuel : ℕ) : ℝ) + 1) := by
  have hbound := runCapped_queryScale_le P Q a rhoMax rhoDr jStar h chop l0 H
    etaReady etaPre deltaShort deltaTerm fuel S hh hbase
  have hcast :
      ((runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).queryScale : ℝ) ≤
          (S.cursor : ℝ) + (((fuel + 1 : ℕ) : ℤ) : ℝ) *
            (transitionSpan h l0 H : ℝ) := by
    exact_mod_cast hbound
  rw [hcursor, transitionSpan_cast] at hcast
  push_cast at hcast
  nlinarith only [hcast]

/-- A terminal outcome's state occurs in the recorded trace. -/
theorem runCapped_terminal_state_mem
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d)
    (terminalState : State d)
    (houtcome : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).outcome = RunOutcome.terminal terminalState) :
    terminalState ∈
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).states := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next S' => simp [runCapped, hout] at houtcome
      | terminal state =>
          simp [runCapped, hout] at houtcome
          subst terminalState
          have hfinal := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S state hout
          rw [hfinal]
          exact runCapped_initial_mem P Q a rhoMax rhoDr jStar h chop l0 H
            etaReady etaPre deltaShort deltaTerm 0 S
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          simp [runCapped, hout] at houtcome
          subst terminalState
          have hfinal := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S state hout
          rw [hfinal]
          exact runCapped_initial_mem P Q a rhoMax rhoDr jStar h chop l0 H
            etaReady etaPre deltaShort deltaTerm (fuel + 1) S
      | next S' =>
          simp only [runCapped, hout] at houtcome ⊢
          exact List.mem_cons_of_mem S (ih S' houtcome)

end

end Selection
end HighContrast
end Homogenization
