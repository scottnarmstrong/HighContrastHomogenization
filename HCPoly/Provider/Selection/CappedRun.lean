/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TransitionGuards

/-!
# The selector run under its transition cap

Fuel counts nonterminal transitions.  At zero fuel the terminal rule may still
return its tuple; a further nonterminal rule instead produces the distinguished
cap-failure outcome.  Thus termination remains a theorem about the execution,
not a side condition of its definition.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

/-- The two possible outcomes of a capped execution. -/
inductive RunOutcome (d : ℕ) where
  | terminal (state : State d)
  | capFailure (state : State d)

/-- The trace and outcome of a capped execution. -/
structure CappedRun (d : ℕ) where
  states : List (State d)
  rules : List TransitionRule
  queryScale : ℤ
  transitionCount : ℕ
  outcome : RunOutcome d

variable {d : ℕ}

/-- The source cap `N_cap = 1 + ⌈C_N Λ⌉`. -/
def transitionCap (CN Lam : ℝ) : ℕ :=
  1 + ⌈CN * Lam⌉₊

/-- Defining equation for the transition cap. -/
theorem transitionCap_eq (CN Lam : ℝ) :
    transitionCap CN Lam = 1 + ⌈CN * Lam⌉₊ := rfl

/-- The cap plus its final read allowance is at most `(C_N+3)Λ`. -/
theorem transitionCap_add_one_le {CN Lam : ℝ} (hCN : 0 ≤ CN) (hLam : 1 ≤ Lam) :
    ((transitionCap CN Lam + 1 : ℕ) : ℝ) ≤ (CN + 3) * Lam := by
  have hLam0 : 0 ≤ Lam := le_trans zero_le_one hLam
  have hx0 : 0 ≤ CN * Lam := mul_nonneg hCN hLam0
  have hceil := Nat.ceil_lt_add_one hx0
  change ((1 + ⌈CN * Lam⌉₊ + 1 : ℕ) : ℝ) ≤ (CN + 3) * Lam
  push_cast
  have hthree : (3 : ℝ) ≤ 3 * Lam := by
    simpa using
      (mul_le_mul_of_nonneg_left hLam (by norm_num : (0 : ℝ) ≤ 3))
  linarith only [hceil, hthree]

/-- Execute at most the supplied number of nonterminal transitions. -/
def runCapped (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) :
    ℕ → State d → CappedRun d
  | 0, S =>
      let step := selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S
      match step.outcome with
      | .next _ =>
          { states := [S]
            rules := []
            queryScale := step.readScale
            transitionCount := 0
            outcome := .capFailure S }
      | .terminal state =>
          { states := [S]
            rules := [step.rule]
            queryScale := step.readScale
            transitionCount := 0
            outcome := .terminal state }
  | fuel + 1, S =>
      let step := selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S
      match step.outcome with
      | .terminal state =>
          { states := [S]
            rules := [step.rule]
            queryScale := step.readScale
            transitionCount := 0
            outcome := .terminal state }
      | .next S' =>
          let tail := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
            etaPre deltaShort deltaTerm fuel S'
          { states := S :: tail.states
            rules := step.rule :: tail.rules
            queryScale := max step.readScale tail.queryScale
            transitionCount := tail.transitionCount + 1
            outcome := tail.outcome }

/-- The number of performed nonterminal transitions never exceeds the fuel. -/
theorem runCapped_transitionCount_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d) :
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).transitionCount ≤ fuel := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;> simp [runCapped, hout]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal result => simp [runCapped, hout]
      | next S' =>
          simpa [runCapped, hout, Nat.succ_eq_add_one] using
            Nat.succ_le_succ (ih S')

/-- The initial state is retained in every capped trace. -/
theorem runCapped_initial_mem
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d) :
    S ∈ (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states := by
  cases fuel with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;> simp [runCapped, hout]
  | succ fuel =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;> simp [runCapped, hout]

end

end Selection
end HighContrast
end Homogenization
