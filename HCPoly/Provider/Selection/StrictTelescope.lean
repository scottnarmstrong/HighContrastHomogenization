/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Termination

/-!
# Potential telescoping on a capped selector trace

The trace itself supplies the finite prefix.  A one-step inequality for every
recorded adjacency therefore telescopes through the executable run, including
the final source state in either outcome.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The outcome state is one of the states retained by the capped execution. -/
theorem runCapped_finalState_mem
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d) :
    runFinalState (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm fuel S) ∈
        (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
          deltaShort deltaTerm fuel S).states := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next Sn => simp [runCapped, hout, runFinalState]
      | terminal T =>
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          simp [runCapped, hout, runFinalState, hstate]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal T =>
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          simp [runCapped, hout, runFinalState, hstate]
      | next Sn =>
          simp only [runCapped, hout, List.mem_cons]
          exact Or.inr (ih Sn)

/-- The outcome state is the last state retained by the capped execution. -/
theorem runCapped_finalState_getLast?
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d) :
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states.getLast? =
        some (runFinalState (runCapped P Q a rhoMax rhoDr jStar h chop l0 H
          etaReady etaPre deltaShort deltaTerm fuel S)) := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next Sn => simp [runCapped, hout, runFinalState]
      | terminal T =>
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          simp [runCapped, hout, runFinalState, hstate]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal T =>
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          simp [runCapped, hout, runFinalState, hstate]
      | next Sn =>
          obtain ⟨states, hstates⟩ := runCapped_states_cons P Q a rhoMax rhoDr
            jStar h chop l0 H etaReady etaPre deltaShort deltaTerm fuel Sn
          simp only [runCapped, hout]
          change
            (S :: (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
              etaPre deltaShort deltaTerm fuel Sn).states).getLast? =
              some (runFinalState (runCapped P Q a rhoMax rhoDr jStar h chop
                l0 H etaReady etaPre deltaShort deltaTerm fuel Sn))
          rw [hstates, List.getLast?_cons_cons]
          have hlast := ih Sn
          rw [hstates] at hlast
          exact hlast

/-- Actual consecutive potential rows telescope over all nonterminal rules of
the capped execution. -/
theorem runCapped_potential_bound_of_consecutive
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d)
    (F : State d → ℝ) {c0 mHop Cdet : ℝ}
    (hstep :
      let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm fuel S
      ∀ i : ℕ, ∀ S₀ S₁ : State d,
        run.states[i]? = some S₀ → run.states[i + 1]? = some S₁ →
          ∃ rule : TransitionRule, run.rules[i]? = some rule ∧
            F S₁ ≤ F S₀ - c0 - mHop *
              (if rule = TransitionRule.t5 then 1 else 0) +
                Cdet * transitionCharge P h l0 H S₀ rule) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S
    c0 * (run.transitionCount : ℝ) +
        mHop * (run.rules.count TransitionRule.t5 : ℝ) ≤
      F S - F (runFinalState run) +
        Cdet * runTransitionSum (transitionCharge P h l0 H) run := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next Sn =>
          simp [runCapped, hout, runFinalState, runTransitionSum,
            pairedTransitionSum]
      | terminal T =>
          have hrule := selectorStep_terminal_rule P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          simp [runCapped, hout, hrule, hstate, runFinalState,
            runTransitionSum, pairedTransitionSum, transitionCharge]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal T =>
          have hrule := selectorStep_terminal_rule P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          simp [runCapped, hout, hrule, hstate, runFinalState,
            runTransitionSum, pairedTransitionSum, transitionCharge]
      | next Sn =>
          let tail := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
            etaPre deltaShort deltaTerm fuel Sn
          obtain ⟨states, hstates⟩ := runCapped_states_cons P Q a rhoMax rhoDr
            jStar h chop l0 H etaReady etaPre deltaShort deltaTerm fuel Sn
          have hzero :
              (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
                deltaShort deltaTerm (fuel + 1) S).states[0]? = some S := by
            simp [runCapped, hout]
          have hone :
              (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
                deltaShort deltaTerm (fuel + 1) S).states[1]? = some Sn := by
            simp [runCapped, hout, hstates]
          obtain ⟨rule, hrule, hfirst⟩ := hstep 0 S Sn hzero hone
          have hlabel :
              (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                etaPre deltaShort deltaTerm S).rule = rule := by
            simpa [runCapped, hout] using hrule
          have htailStep : ∀ i : ℕ, ∀ S₀ S₁ : State d,
              tail.states[i]? = some S₀ → tail.states[i + 1]? = some S₁ →
                ∃ rule : TransitionRule, tail.rules[i]? = some rule ∧
                  F S₁ ≤ F S₀ - c0 - mHop *
                    (if rule = TransitionRule.t5 then 1 else 0) +
                      Cdet * transitionCharge P h l0 H S₀ rule := by
            intro i S₀ S₁ h₀ h₁
            have h₀' :
                (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
                  deltaShort deltaTerm (fuel + 1) S).states[i + 1]? = some S₀ := by
              simpa only [runCapped, hout, List.getElem?_cons_succ, tail] using h₀
            have h₁' :
                (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
                  deltaShort deltaTerm (fuel + 1) S).states[(i + 1) + 1]? =
                    some S₁ := by
              simpa only [runCapped, hout, List.getElem?_cons_succ, tail,
                add_assoc, Nat.add_left_comm, Nat.add_comm] using h₁
            obtain ⟨rule, hrule, hrow⟩ := hstep (i + 1) S₀ S₁ h₀' h₁'
            refine ⟨rule, ?_, hrow⟩
            simpa only [runCapped, hout, List.getElem?_cons_succ, tail] using hrule
          have htail := ih Sn htailStep
          dsimp only at htail
          rw [← hlabel] at hfirst
          by_cases hrule5 :
              (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                etaPre deltaShort deltaTerm S).rule = TransitionRule.t5
          · simp only [runCapped, hout, Nat.cast_add, Nat.cast_one,
              List.count_cons, beq_iff_eq, hrule5, if_true, runTransitionSum,
              pairedTransitionSum, runFinalState] at htail ⊢
            simp only [hrule5, if_true] at hfirst
            ring_nf at hfirst htail ⊢
            linarith only [hfirst, htail]
          · simp only [runCapped, hout, Nat.cast_add, Nat.cast_one,
              List.count_cons, beq_iff_eq, hrule5, if_false, runTransitionSum,
              pairedTransitionSum, runFinalState] at htail ⊢
            simp only [hrule5, if_false] at hfirst
            ring_nf at hfirst htail ⊢
            linarith only [hfirst, htail]

end

end Homogenization.HighContrast.Selection
