/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TransitionTrace

/-!
# Counting and terminal bounds for selector traces

The stage is exactly the number of successful path steps recorded before the
last reached state.  Consequently both the T5 count and the final stage are
bounded by the number of nonterminal transitions and by the original fuel.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The number of recorded T5 rules is at most the number of nonterminal
transitions. -/
theorem runCapped_t5_count_le_transitionCount
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d) :
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).rules.count TransitionRule.t5 ≤
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).transitionCount := by
  induction fuel generalizing S with
  | zero =>
      cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
          deltaShort deltaTerm l0 H S <;>
        simp [runCapped, selectorStep, hrule]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          have hrule := selectorStep_terminal_rule P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S state hout
          simp [runCapped, hout, hrule]
      | next Sn =>
          by_cases hrule : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H
            etaReady etaPre deltaShort deltaTerm S).rule = TransitionRule.t5
          · simpa [runCapped, hout, hrule] using Nat.succ_le_succ (ih Sn)
          · exact (by
              simp only [runCapped, hout, List.count_cons, beq_iff_eq, hrule,
                if_false]
              exact Nat.le_succ_of_le (ih Sn))

/-- The recorded T5 count is bounded by the original fuel. -/
theorem runCapped_t5_count_le_fuel
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d) :
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).rules.count TransitionRule.t5 ≤ fuel :=
  (runCapped_t5_count_le_transitionCount P Q a rhoMax rhoDr jStar h chop l0 H
    etaReady etaPre deltaShort deltaTerm fuel S).trans
    (runCapped_transitionCount_le P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm fuel S)

/-- A successful run's terminal source state is the last reached state. -/
theorem runCapped_terminal_getLast?
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S T : State d)
    (houtcome : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).outcome = RunOutcome.terminal T) :
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states.getLast? = some T := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next Sn => simp [runCapped, hout] at houtcome
      | terminal state =>
          simp [runCapped, hout] at houtcome ⊢
          subst T
          exact (selectorStep_terminal_state P Q a rhoMax rhoDr jStar h chop l0
            H etaReady etaPre deltaShort deltaTerm S state hout).symm
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          simp [runCapped, hout] at houtcome ⊢
          subst T
          exact (selectorStep_terminal_state P Q a rhoMax rhoDr jStar h chop l0
            H etaReady etaPre deltaShort deltaTerm S state hout).symm
      | next Sn =>
          simp only [runCapped, hout] at houtcome ⊢
          obtain ⟨tail, htail⟩ := runCapped_states_cons P Q a rhoMax rhoDr
            jStar h chop l0 H etaReady etaPre deltaShort deltaTerm fuel Sn
          have hlast := ih Sn houtcome
          rw [htail] at hlast
          rw [htail, List.getLast?_cons_cons]
          exact hlast

/-- The last reached stage is the initial stage plus the number of T5 rules. -/
theorem runCapped_last_stage_eq
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S T : State d)
    (hlast : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states.getLast? = some T) :
    T.stage = S.stage +
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).rules.count TransitionRule.t5 := by
  induction fuel generalizing S T with
  | zero =>
      cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
          deltaShort deltaTerm l0 H S <;>
        simp [runCapped, selectorStep, hrule] at hlast ⊢
      all_goals (subst T; simp)
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          have hrule := selectorStep_terminal_rule P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S state hout
          simp [runCapped, hout, hrule] at hlast ⊢
          subst T
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S state hout
          subst state
          simp
      | next Sn =>
          obtain ⟨tail, htail⟩ := runCapped_states_cons P Q a rhoMax rhoDr
            jStar h chop l0 H etaReady etaPre deltaShort deltaTerm fuel Sn
          have htailLast :
              (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
                deltaShort deltaTerm fuel Sn).states.getLast? = some T := by
            rw [htail]
            simp only [runCapped, hout] at hlast
            rw [htail, List.getLast?_cons_cons] at hlast
            exact hlast
          have hstage := selectorStep_next_stage P Q a rhoMax rhoDr jStar h chop
            l0 H etaReady etaPre deltaShort deltaTerm S Sn hout
          have hind := ih Sn T htailLast
          by_cases hrule : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H
            etaReady etaPre deltaShort deltaTerm S).rule = TransitionRule.t5
          · simp [runCapped, hout, hrule] at hstage ⊢
            omega
          · simp [runCapped, hout, hrule] at hstage ⊢
            omega

/-- From a stage-zero start, the last reached stage is bounded by both the
nonterminal transition count and the fuel. -/
theorem runCapped_last_stage_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S T : State d)
    (hstage : S.stage = 0)
    (hlast : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states.getLast? = some T) :
    T.stage ≤
        (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
          deltaShort deltaTerm fuel S).transitionCount ∧
      T.stage ≤ fuel := by
  rw [runCapped_last_stage_eq P Q a rhoMax rhoDr jStar h chop l0 H etaReady
    etaPre deltaShort deltaTerm fuel S T hlast, hstage, zero_add]
  exact ⟨runCapped_t5_count_le_transitionCount P Q a rhoMax rhoDr jStar h chop
      l0 H etaReady etaPre deltaShort deltaTerm fuel S,
    runCapped_t5_count_le_fuel P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm fuel S⟩

end

end Selection
end HighContrast
end Homogenization
