/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.State

/-!
# Ordered transitions of the global selector

The seven rules are selected by an exhaustive ordered partition of the current
state.  Every test is annealed.  A successful short test changes grid along the
fixed projective path, while all other nonterminal rules remain on the current
grid.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The labels of the seven ordered transition rules. -/
inductive TransitionRule where
  | t1
  | t2
  | t3
  | t4
  | t5
  | t6
  | t7
deriving DecidableEq

/-- The law-determined tuple formed from a stopped state and its retained
candidate. -/
structure TerminalData (d : ℕ) where
  finalState : State d
  E0 : BlockMat d
  m0 : Mat d
  q : Mat d
  s : ℤ
  t : ℤ

/-- A single rule either advances to another state or stops at the current
state.  The terminal tuple is formed only after the terminal invariant supplies
the retained candidate. -/
inductive StepOutcome (d : ℕ) where
  | next (state : State d)
  | terminal (state : State d)

/-- The selected rule, its largest read scale, and its outcome. -/
structure StepResult (d : ℕ) where
  rule : TransitionRule
  readScale : ℤ
  outcome : StepOutcome d

variable {d : ℕ}

/-- The short determinant test fails when its root quotient is too large. -/
def shortTestFails (P : Measure (CoeffSpace d)) (deltaShort : ℝ) (l0 : ℕ)
    (S : State d) : Prop :=
  1 + deltaShort <
    adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + 2 * (l0 : ℤ))

/-- Characterization of the failed short test. -/
theorem shortTestFails_iff (P : Measure (CoeffSpace d)) (deltaShort : ℝ)
    (l0 : ℕ) (S : State d) :
    shortTestFails P deltaShort l0 S ↔
      1 + deltaShort <
        adaptedDetRoot P S.q S.cursor /
          adaptedDetRoot P S.q (S.cursor + 2 * (l0 : ℤ)) := Iff.rfl

/-- The terminal determinant test fails at weak equality as well. -/
def terminalTestFails (P : Measure (CoeffSpace d)) (deltaTerm : ℝ) (H : ℕ)
    (S : State d) : Prop :=
  1 + deltaTerm ≤
    adaptedDetRoot P S.q S.base /
      adaptedDetRoot P S.q (S.base + (H : ℤ))

/-- Characterization of the failed terminal test. -/
theorem terminalTestFails_iff (P : Measure (CoeffSpace d)) (deltaTerm : ℝ)
    (H : ℕ) (S : State d) :
    terminalTestFails P deltaTerm H S ↔
      1 + deltaTerm ≤
        adaptedDetRoot P S.q S.base /
          adaptedDetRoot P S.q (S.base + (H : ℤ)) := Iff.rfl

/-- The guard attached to each rule in the ordered partition Root--T7. -/
def ruleGuard (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar : ℤ) (etaReady etaPre deltaShort deltaTerm : ℝ) (l0 H : ℕ)
    (rule : TransitionRule) (S : State d) : Prop :=
  match rule with
  | .t1 => S.phase = .fresh
  | .t2 => S.phase = .search ∧ 0 < driftIndex P rhoDr etaPre jStar S
  | .t3 => S.phase = .search ∧ driftIndex P rhoDr etaPre jStar S = 0 ∧
      ENNReal.ofReal etaReady < stateProfile P Q a rhoMax jStar S
  | .t4 => S.phase = .search ∧ driftIndex P rhoDr etaPre jStar S = 0 ∧
      stateProfile P Q a rhoMax jStar S ≤ ENNReal.ofReal etaReady ∧
      shortTestFails P deltaShort l0 S
  | .t5 => S.phase = .search ∧ driftIndex P rhoDr etaPre jStar S = 0 ∧
      stateProfile P Q a rhoMax jStar S ≤ ENNReal.ofReal etaReady ∧
      ¬shortTestFails P deltaShort l0 S
  | .t6 => S.phase = .terminal ∧ terminalTestFails P deltaTerm H S
  | .t7 => S.phase = .terminal ∧ ¬terminalTestFails P deltaTerm H S

/-- The first rule whose guard holds. -/
def selectedRule (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar : ℤ) (etaReady etaPre deltaShort deltaTerm : ℝ) (l0 H : ℕ)
    (S : State d) : TransitionRule :=
  match S.phase with
  | .fresh => .t1
  | .search =>
      if 0 < driftIndex P rhoDr etaPre jStar S then .t2
      else if ENNReal.ofReal etaReady < stateProfile P Q a rhoMax jStar S then .t3
      else if shortTestFails P deltaShort l0 S then .t4 else .t5
  | .terminal => if terminalTestFails P deltaTerm H S then .t6 else .t7

/-- The T5 state on the new rounded grid. -/
def hopState (P : Measure (CoeffSpace d)) (Q a rhoMax : ℝ) (jStar : ℤ)
    (chop : ℝ) (l0 : ℕ) (S : State d) : State d :=
  let t0 := S.cursor + 2 * (l0 : ℤ)
  let n := S.cursor + (l0 : ℤ)
  let F := adaptedMean P S.q t0
  let mu' := projPathStep chop S.mu (canonicalMetric F)
  let q' := roundedGrid jStar mu'
  let final := projDist S.mu (canonicalMetric F) ≤ chop
  { stage := S.stage + 1
    q := q'
    mu := mu'
    base := n
    baseMean := adaptedMean P q' n
    checkpoint := n
    centered := centeredHistory P Q rhoMax q' jStar n
    nonlinear := nonlinearHistory P Q a q' jStar n
    cursor := n
    phase := if final then .terminal else .fresh
    candidate := if final then some F else none
    prefixLoss := S.prefixLoss + detLoss P S.q S.cursor t0 }

/-- One deterministic evaluation of the ordered rules Root--T7. -/
def selectorStep (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S : State d) : StepResult d :=
  match selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre deltaShort
      deltaTerm l0 H S with
  | .t1 =>
      { rule := .t1, readScale := S.cursor + h,
        outcome := .next (advanceCursor P S (S.cursor + h) .search none) }
  | .t2 =>
      { rule := .t2, readScale := S.cursor + h,
        outcome := .next (advanceCursor P S (S.cursor + h) .search none) }
  | .t3 =>
      { rule := .t3, readScale := S.cursor + h,
        outcome := .next (advanceCursor P S (S.cursor + h) .search none) }
  | .t4 =>
      { rule := .t4, readScale := S.cursor + 2 * (l0 : ℤ),
        outcome := .next
          (advanceCursor P S (S.cursor + 2 * (l0 : ℤ)) .search none) }
  | .t5 =>
      { rule := .t5, readScale := S.cursor + 2 * (l0 : ℤ),
        outcome := .next (hopState P Q a rhoMax jStar chop l0 S) }
  | .t6 =>
      { rule := .t6, readScale := S.base + max (H : ℤ) h,
        outcome := .next
          (advanceCursor P S (S.base + max (H : ℤ) h) .search none) }
  | .t7 =>
      { rule := .t7, readScale := S.base + (H : ℤ),
        outcome := .terminal S }

/-- The integer form of the largest scale span read by one rule. -/
def transitionSpan (h : ℤ) (l0 H : ℕ) : ℤ :=
  max h (max (2 * (l0 : ℤ)) (H : ℤ))

end

end Selection
end HighContrast
end Homogenization
