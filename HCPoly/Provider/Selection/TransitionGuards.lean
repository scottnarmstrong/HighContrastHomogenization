/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Transitions

/-!
# Exhaustiveness and scale bounds for selector transitions

The ordered rule selector assigns every state to exactly one of Root--T7.  The
same case split also shows that one rule reads and advances by at most the
common execution span.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The weak complement of the failed short test is the determinant-root
inequality consumed by the short-hop provider. -/
theorem shortTest_passes_iff (P : Measure (CoeffSpace d)) (deltaShort : ℝ)
    (l0 : ℕ) (S : State d)
    (hroot : 0 < adaptedDetRoot P S.q (S.cursor + 2 * (l0 : ℤ))) :
    ¬shortTestFails P deltaShort l0 S ↔
      adaptedDetRoot P S.q S.cursor ≤
        (1 + deltaShort) *
          adaptedDetRoot P S.q (S.cursor + 2 * (l0 : ℤ)) := by
  rw [shortTestFails_iff, not_lt]
  exact div_le_iff₀ hroot

/-- The strict complement of the failed terminal test is the terminal
determinant inequality. -/
theorem terminalTest_passes_iff (P : Measure (CoeffSpace d)) (deltaTerm : ℝ)
    (H : ℕ) (S : State d)
    (hroot : 0 < adaptedDetRoot P S.q (S.base + (H : ℤ))) :
    ¬terminalTestFails P deltaTerm H S ↔
      adaptedDetRoot P S.q S.base <
        (1 + deltaTerm) * adaptedDetRoot P S.q (S.base + (H : ℤ)) := by
  rw [terminalTestFails_iff, not_le]
  exact div_lt_iff₀ hroot

/-- The selected guard holds, including every equality boundary. -/
theorem selectedRule_guard (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar : ℤ) (etaReady etaPre deltaShort deltaTerm : ℝ) (l0 H : ℕ)
    (S : State d) :
    ruleGuard P Q a rhoMax rhoDr jStar etaReady etaPre deltaShort deltaTerm
      l0 H (selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre deltaShort
        deltaTerm l0 H S) S := by
  cases hphase : S.phase with
  | fresh => simp [selectedRule, ruleGuard, hphase]
  | search =>
      by_cases hb : 0 < driftIndex P rhoDr etaPre jStar S
      · simp [selectedRule, ruleGuard, hphase, hb]
      · have hb0 : driftIndex P rhoDr etaPre jStar S = 0 := Nat.eq_zero_of_not_pos hb
        by_cases hp : ENNReal.ofReal etaReady < stateProfile P Q a rhoMax jStar S
        · simp [selectedRule, ruleGuard, hphase, hb0, hp]
        · have hp' : stateProfile P Q a rhoMax jStar S ≤ ENNReal.ofReal etaReady :=
            le_of_not_gt hp
          by_cases hs : shortTestFails P deltaShort l0 S
          · simp [selectedRule, ruleGuard, hphase, hb0, hp, hp', hs]
          · simp [selectedRule, ruleGuard, hphase, hb0, hp, hp', hs]
  | terminal =>
      by_cases ht : terminalTestFails P deltaTerm H S
      · simp [selectedRule, ruleGuard, hphase, ht]
      · simp [selectedRule, ruleGuard, hphase, ht]

/-- A rule whose guard holds is the uniquely selected rule. -/
theorem ruleGuard_unique (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar : ℤ) (etaReady etaPre deltaShort deltaTerm : ℝ) (l0 H : ℕ)
    (S : State d) (rule : TransitionRule)
    (hguard : ruleGuard P Q a rhoMax rhoDr jStar etaReady etaPre deltaShort
      deltaTerm l0 H rule S) :
    rule = selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre deltaShort
      deltaTerm l0 H S := by
  cases rule with
  | t1 =>
      simp only [ruleGuard] at hguard
      simp [selectedRule, hguard]
  | t2 =>
      simp only [ruleGuard] at hguard
      rcases hguard with ⟨hphase, hb⟩
      simp [selectedRule, hphase, hb]
  | t3 =>
      simp only [ruleGuard] at hguard
      rcases hguard with ⟨hphase, hb, hp⟩
      have hnb : ¬0 < driftIndex P rhoDr etaPre jStar S := by omega
      simp [selectedRule, hphase, hnb, hp]
  | t4 =>
      simp only [ruleGuard] at hguard
      rcases hguard with ⟨hphase, hb, hp, hs⟩
      have hnb : ¬0 < driftIndex P rhoDr etaPre jStar S := by omega
      have hnp : ¬ENNReal.ofReal etaReady < stateProfile P Q a rhoMax jStar S :=
        not_lt_of_ge hp
      simp [selectedRule, hphase, hnb, hnp, hs]
  | t5 =>
      simp only [ruleGuard] at hguard
      rcases hguard with ⟨hphase, hb, hp, hs⟩
      have hnb : ¬0 < driftIndex P rhoDr etaPre jStar S := by omega
      have hnp : ¬ENNReal.ofReal etaReady < stateProfile P Q a rhoMax jStar S :=
        not_lt_of_ge hp
      simp [selectedRule, hphase, hnb, hnp, hs]
  | t6 =>
      simp only [ruleGuard] at hguard
      rcases hguard with ⟨hphase, ht⟩
      simp [selectedRule, hphase, ht]
  | t7 =>
      simp only [ruleGuard] at hguard
      rcases hguard with ⟨hphase, ht⟩
      simp [selectedRule, hphase, ht]

/-- The integer execution span is nonnegative. -/
theorem transitionSpan_nonneg {h : ℤ} (hh : 0 ≤ h) (l0 H : ℕ) :
    0 ≤ transitionSpan h l0 H :=
  le_trans hh (le_max_left _ _)

/-- One rule reads no farther than one execution span beyond the cursor. -/
theorem selectorStep_readScale_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S : State d)
    (hbase : S.base ≤ S.cursor) :
    (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).readScale ≤ S.cursor + transitionSpan h l0 H := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;>
    simp [selectorStep, hrule, transitionSpan] <;> omega

/-- A nonterminal rule moves the cursor by at most one execution span. -/
theorem selectorStep_next_cursor_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S S' : State d)
    (hbase : S.base ≤ S.cursor)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.next S') :
    S'.cursor ≤ S.cursor + transitionSpan h l0 H := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S
  all_goals simp [selectorStep, hrule] at hout
  all_goals subst S'
  all_goals simp [advanceCursor, hopState, transitionSpan]
  all_goals omega

/-- Every nonterminal update preserves the ordering of the stage base and the
cursor. -/
theorem selectorStep_next_base_le_cursor
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S S' : State d)
    (hh : 0 ≤ h) (hbase : S.base ≤ S.cursor)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.next S') :
    S'.base ≤ S'.cursor := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S
  all_goals simp [selectorStep, hrule] at hout
  all_goals subst S'
  all_goals simp [advanceCursor, hopState]
  all_goals omega

/-- A terminal step stops at the current state. -/
theorem selectorStep_terminal_state
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S : State d)
    (S' : State d)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.terminal S') :
    S' = S := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;>
    simp [selectorStep, hrule] at hout
  exact hout.symm

end

end Selection
end HighContrast
end Homogenization
