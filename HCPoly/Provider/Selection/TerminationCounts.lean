/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TransitionTraceBounds

/-!
# Structural termination counts for the selector

The capped runner records only genuine nonterminal transitions in its
transition count.  A cap failure therefore uses all available fuel, while a
strict count bound forces a terminal outcome.  The rule labels also give the
two branch-count identities used after termination.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A cap failure occurs only after every available nonterminal transition has
been used. -/
theorem runCapped_capFailure_transitionCount_eq
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S T : State d)
    (houtcome : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm fuel S).outcome = RunOutcome.capFailure T) :
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).transitionCount = fuel := by
  induction fuel generalizing S T with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;> simp [runCapped, hout]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state => simp [runCapped, hout] at houtcome
      | next S' =>
          simp only [runCapped, hout] at houtcome ⊢
          rw [ih S' T houtcome]

/-- A run whose nonterminal count is strictly below its fuel has reached the
terminal rule. -/
theorem runCapped_terminal_of_transitionCount_lt_fuel
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d)
    (hcount : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).transitionCount < fuel) :
    ∃ T : State d,
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).outcome = RunOutcome.terminal T := by
  cases houtcome : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
    etaPre deltaShort deltaTerm fuel S).outcome with
  | terminal T => exact ⟨T, rfl⟩
  | capFailure T =>
      have heq := runCapped_capFailure_transitionCount_eq P Q a rhoMax rhoDr
        jStar h chop l0 H etaReady etaPre deltaShort deltaTerm fuel S T houtcome
      omega

end

end Selection
end HighContrast
end Homogenization
