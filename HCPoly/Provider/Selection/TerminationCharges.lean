/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Charges
import HCPoly.Provider.Selection.TerminationCounts

/-!
# Charge accounting along selector traces

The determinant loss stored by the selector is exactly the sum of its
completed fixed-grid stages and the current partial stage.  This is a purely
structural fact about the actual capped execution.  It is kept separate from
the later comparison of completed stages across different rounded grids.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Components of a transition charge -/

/-- The ordinary cursor interval read by a transition. -/
def ordinaryTransitionCharge (P : Measure (CoeffSpace d)) (h : ℤ) (l0 H : ℕ)
    (S : State d) : TransitionRule → ℝ
  | .t1 => detLoss P S.q S.cursor (S.cursor + h)
  | .t2 => detLoss P S.q S.cursor (S.cursor + h)
  | .t3 => detLoss P S.q S.cursor (S.cursor + h)
  | .t4 => detLoss P S.q S.cursor (S.cursor + 2 * (l0 : ℤ))
  | .t5 => detLoss P S.q S.cursor (S.cursor + 2 * (l0 : ℤ))
  | .t6 => detLoss P S.q S.base (S.base + max (H : ℤ) h)
  | .t7 => 0

/-- The completed-stage summary inserted by a successful short hop. -/
def completedStageCharge (P : Measure (CoeffSpace d)) (l0 : ℕ)
    (S : State d) : TransitionRule → ℝ
  | .t5 => detLoss P S.q S.base (S.cursor + 2 * (l0 : ℤ))
  | _ => 0

/-- The synchronized service term attached precisely to T2 and T3. -/
def serviceTransitionCharge (P : Measure (CoeffSpace d)) (h : ℤ)
    (S : State d) : TransitionRule → ℝ
  | .t2 => serviceWindowCharge P S.q h S.cursor
  | .t3 => serviceWindowCharge P S.q h S.cursor
  | _ => 0

/-- Every transition charge is the sum of its ordinary interval, completed
stage summary, and synchronized service term. -/
theorem transitionCharge_eq_components (P : Measure (CoeffSpace d)) (h : ℤ)
    (l0 H : ℕ) (S : State d) (rule : TransitionRule) :
    transitionCharge P h l0 H S rule =
      ordinaryTransitionCharge P h l0 H S rule +
        completedStageCharge P l0 S rule +
          serviceTransitionCharge P h S rule := by
  cases rule <;> simp [transitionCharge, ordinaryTransitionCharge,
    completedStageCharge, serviceTransitionCharge]

/-! ## Finite trace sums -/

/-- Sum a state-dependent quantity over aligned state and rule lists. -/
def pairedTransitionSum (f : State d → TransitionRule → ℝ) :
    List (State d) → List TransitionRule → ℝ
  | S :: states, rule :: rules =>
      f S rule + pairedTransitionSum f states rules
  | _, _ => 0

/-- Sum a state-dependent quantity over the aligned entries of a capped run. -/
def runTransitionSum (f : State d → TransitionRule → ℝ)
    (run : CappedRun d) : ℝ :=
  pairedTransitionSum f run.states run.rules

/-- The last state reached by either outcome of a capped run. -/
def runFinalState (run : CappedRun d) : State d :=
  match run.outcome with
  | .terminal S => S
  | .capFailure S => S

/-- Defining equation for the last reached state. -/
theorem runFinalState_eq (run : CappedRun d) :
    runFinalState run =
      match run.outcome with
      | .terminal S => S
      | .capFailure S => S := rfl

/-- The total transition charge splits exactly into the three finite trace
sums. -/
theorem runTransitionSum_transitionCharge_eq (P : Measure (CoeffSpace d))
    (h : ℤ) (l0 H : ℕ) (run : CappedRun d) :
    runTransitionSum (transitionCharge P h l0 H) run =
      runTransitionSum (ordinaryTransitionCharge P h l0 H) run +
        runTransitionSum (completedStageCharge P l0) run +
          runTransitionSum (serviceTransitionCharge P h) run := by
  rw [runTransitionSum, runTransitionSum, runTransitionSum, runTransitionSum]
  have hsum : ∀ (states : List (State d)) (rules : List TransitionRule),
      pairedTransitionSum (transitionCharge P h l0 H) states rules =
        pairedTransitionSum (ordinaryTransitionCharge P h l0 H) states rules +
          pairedTransitionSum (completedStageCharge P l0) states rules +
            pairedTransitionSum (serviceTransitionCharge P h) states rules := by
    intro states rules
    induction states generalizing rules with
    | nil => simp [pairedTransitionSum]
    | cons S states ih =>
        cases rules with
        | nil => simp [pairedTransitionSum]
        | cons rule rules =>
            simp only [pairedTransitionSum]
            rw [transitionCharge_eq_components, ih]
            ring
  exact hsum run.states run.rules

/-! ## Exact prefix accounting -/

/-- Determinant-root losses concatenate exactly on a fixed grid. -/
theorem detLoss_add (P : Measure (CoeffSpace d)) (q : Mat d) (u v w : ℤ) :
    detLoss P q u v + detLoss P q v w = detLoss P q u w := by
  rw [detLoss, detLoss, detLoss]
  ring

/-- A zero-length determinant-root loss vanishes. -/
theorem detLoss_self (P : Measure (CoeffSpace d)) (q : Mat d) (u : ℤ) :
    detLoss P q u u = 0 := by
  rw [detLoss]
  ring

private theorem selectorStep_next_phaseBase
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S Sn : State d)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.next Sn) :
    Sn.phase = Phase.fresh ∨ Sn.phase = Phase.terminal →
      Sn.base = Sn.cursor := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;>
    simp [selectorStep, hrule, advanceCursor, hopState] at hout ⊢
  all_goals subst_vars
  all_goals simp_all

private theorem selectorStep_next_ordinaryCharge
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S Sn : State d)
    (halign : S.phase = Phase.fresh ∨ S.phase = Phase.terminal →
      S.base = S.cursor)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.next Sn) :
    ordinaryTransitionCharge P h l0 H S
        (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
          deltaShort deltaTerm S).rule + S.prefixLoss = Sn.prefixLoss := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S with
  | t1 | t2 | t3 | t4 | t5 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      simp [selectorStep, hrule, advanceCursor, hopState,
        ordinaryTransitionCharge, add_comm]
  | t6 =>
      have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
      rw [hrule] at hguard
      have hphase : S.phase = Phase.terminal := by
        simpa only [ruleGuard] using hguard.1
      have hbase : S.base = S.cursor := halign (Or.inr hphase)
      simp [selectorStep, hrule] at hout
      subst Sn
      simp [selectorStep, hrule, advanceCursor, ordinaryTransitionCharge,
        hbase, add_comm]
  | t7 => simp [selectorStep, hrule] at hout

private theorem selectorStep_next_stageCharge
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S Sn : State d)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.next Sn) :
    completedStageCharge P l0 S
          (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
            deltaShort deltaTerm S).rule +
        detLoss P Sn.q Sn.base Sn.cursor =
      Sn.prefixLoss - S.prefixLoss + detLoss P S.q S.base S.cursor := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S with
  | t1 | t2 | t3 | t4 | t6 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [selectorStep, hrule, completedStageCharge, advanceCursor]
      rw [← detLoss_add P S.q S.base S.cursor]
      ring
  | t5 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [selectorStep, hrule, completedStageCharge, hopState]
      rw [detLoss_self, add_zero, ← detLoss_add P S.q S.base S.cursor]
      ring
  | t7 => simp [selectorStep, hrule] at hout

private theorem runCapped_chargeAccounting
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S : State d)
    (halign : S.phase = Phase.fresh ∨ S.phase = Phase.terminal →
      S.base = S.cursor) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S
    runTransitionSum (ordinaryTransitionCharge P h l0 H) run + S.prefixLoss =
        (runFinalState run).prefixLoss ∧
      runTransitionSum (completedStageCharge P l0) run +
          detLoss P (runFinalState run).q (runFinalState run).base
            (runFinalState run).cursor =
        (runFinalState run).prefixLoss - S.prefixLoss +
          detLoss P S.q S.base S.cursor := by
  induction fuel generalizing S with
  | zero =>
      cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
          deltaShort deltaTerm l0 H S <;>
        simp [runCapped, selectorStep, hrule, runTransitionSum,
          pairedTransitionSum, runFinalState, ordinaryTransitionCharge,
          completedStageCharge]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal T =>
          have hrule := selectorStep_terminal_rule P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          subst T
          simp [runCapped, hout, hrule, runTransitionSum, pairedTransitionSum,
            runFinalState, ordinaryTransitionCharge, completedStageCharge]
      | next Sn =>
          have halign' := selectorStep_next_phaseBase P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S Sn hout
          have hstep := selectorStep_next_ordinaryCharge P Q a rhoMax rhoDr
            jStar h chop l0 H etaReady etaPre deltaShort deltaTerm S Sn halign hout
          have hstageStep := selectorStep_next_stageCharge P Q a rhoMax rhoDr
            jStar h chop l0 H etaReady etaPre deltaShort deltaTerm S Sn hout
          have htail := ih Sn halign'
          rcases htail with ⟨hordinary, hstage⟩
          simp only [runCapped, hout, runTransitionSum, pairedTransitionSum]
          let tail := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
            etaPre deltaShort deltaTerm fuel Sn
          change
            ordinaryTransitionCharge P h l0 H S
                  (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                    etaPre deltaShort deltaTerm S).rule +
                runTransitionSum (ordinaryTransitionCharge P h l0 H) tail +
                  S.prefixLoss = (runFinalState tail).prefixLoss ∧
            completedStageCharge P l0 S
                  (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                    etaPre deltaShort deltaTerm S).rule +
                runTransitionSum (completedStageCharge P l0) tail +
                detLoss P (runFinalState tail).q (runFinalState tail).base
                  (runFinalState tail).cursor =
              (runFinalState tail).prefixLoss - S.prefixLoss +
                detLoss P S.q S.base S.cursor
          constructor
          · linarith only [hstep, hordinary]
          · linarith only [hstageStep, hstage]

/-- Along a capped run from the initialized state, the ordinary cursor charges
sum exactly to the stored determinant prefix. -/
theorem runCapped_initial_ordinaryChargeSum_eq
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h r0 : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
    runTransitionSum (ordinaryTransitionCharge P h l0 H) run =
      (runFinalState run).prefixLoss := by
  have haccount := (runCapped_chargeAccounting P Q a rhoMax rhoDr jStar h chop
    l0 H fuel etaReady etaPre deltaShort deltaTerm
    (initialState r0 A0 hcen hnl) (by simp [initialState])).1
  simpa only [initialState, add_zero] using haccount

/-- Along a capped run from the initialized state, the completed T5 summaries
plus the final partial stage are exactly the stored determinant prefix. -/
theorem runCapped_initial_stage_decomposition
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h r0 : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
    runTransitionSum (completedStageCharge P l0) run +
        detLoss P (runFinalState run).q (runFinalState run).base
          (runFinalState run).cursor =
      (runFinalState run).prefixLoss := by
  have haccount := (runCapped_chargeAccounting P Q a rhoMax rhoDr jStar h chop
    l0 H fuel etaReady etaPre deltaShort deltaTerm
    (initialState r0 A0 hcen hnl) (by simp [initialState])).2
  simpa only [initialState, sub_zero, detLoss_self, add_zero] using haccount

end

end Selection
end HighContrast
end Homogenization
