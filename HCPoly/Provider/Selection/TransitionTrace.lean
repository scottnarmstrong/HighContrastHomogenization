/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.RunBounds

/-!
# Structural facts about selector traces

The capped execution stores states and rule labels as ordinary data.  This file
relates adjacent entries to the deterministic step function and records the
stage, grid, prefix-loss, and terminal-state consequences needed by the global
assembly.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A terminal step is exactly the stopping rule T7. -/
theorem selectorStep_terminal_rule
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S S' : State d)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.terminal S') :
    (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).rule = TransitionRule.t7 := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;> simp [selectorStep, hrule] at hout ⊢

/-- The stage increases by one exactly at a recorded T5 step. -/
theorem selectorStep_next_stage
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S S' : State d)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.next S') :
    S'.stage =
      if (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
          deltaShort deltaTerm S).rule = TransitionRule.t5 then
        S.stage + 1
      else S.stage := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;>
    simp [selectorStep, hrule, advanceCursor, hopState] at hout ⊢
  all_goals subst_vars
  all_goals simp

/-- Every capped trace starts with the supplied initial state. -/
theorem runCapped_states_cons
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d) :
    ∃ tail : List (State d),
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).states = S :: tail := by
  cases fuel with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;>
        simp [runCapped, hout]
  | succ fuel =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;>
        simp [runCapped, hout]

/-- Consecutive recorded states and their rule label come from `selectorStep`. -/
theorem runCapped_consecutive
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d)
    {i : ℕ} {S₀ S₁ : State d}
    (h₀ : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states[i]? = some S₀)
    (h₁ : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states[i + 1]? = some S₁) :
    ∃ rule : TransitionRule,
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).rules[i]? = some rule ∧
      (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm S₀).rule = rule ∧
      (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm S₀).outcome = StepOutcome.next S₁ := by
  induction fuel generalizing S i S₀ S₁ with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;>
        cases i <;> simp [runCapped, hout] at h₁
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          cases i <;> simp [runCapped, hout] at h₁
      | next Sn =>
          cases i with
          | zero =>
              obtain ⟨tail, htail⟩ := runCapped_states_cons P Q a rhoMax rhoDr
                jStar h chop l0 H etaReady etaPre deltaShort deltaTerm fuel Sn
              simp [runCapped, hout] at h₀
              subst S₀
              simp [runCapped, hout, htail] at h₁
              subst S₁
              exact ⟨(selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                etaPre deltaShort deltaTerm S).rule, by simp [runCapped, hout], rfl, hout⟩
          | succ i =>
              simp only [runCapped, hout, List.getElem?_cons_succ] at h₀ h₁ ⊢
              exact ih Sn h₀ h₁

end

end Selection
end HighContrast
end Homogenization
