/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TerminationServiceMultiplicity

/-!
# Synchronized-service accounting on an actual selector run

The one-step moving-window account propagates through the executable capped
trace.  Aligned positivity and mean order then turn its last outstanding
window into the current determinant-prefix loss.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem cursor_le_selectorStep_readScale
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm completed service : ℝ)
    (S : State d) (hh : 1 ≤ h)
    (haccount : ServiceAccount P h completed service S) :
    S.cursor ≤ (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm S).readScale := by
  have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady etaPre
    deltaShort deltaTerm l0 H S
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S with
  | t1 | t2 | t3 | t4 | t5 =>
      simp [selectorStep, hrule] <;> omega
  | t6 | t7 =>
      rw [hrule] at hguard
      have hphase : S.phase = Phase.terminal := by
        exact hguard.1
      rw [serviceAccount_eq, hphase] at haccount
      (simp [selectorStep, hrule]; omega)

/-- The service account propagates through every performed transition of a
capped run. -/
theorem runCapped_serviceAccount
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm completed service : ℝ)
    (S : State d) (hh : 1 ≤ h)
    (haccount : ServiceAccount P h completed service S)
    (hmono :
      let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm fuel S
      ∀ S' ∈ run.states, ∀ u v : ℤ, S'.base ≤ u → u ≤ v →
        v ≤ run.queryScale →
          Real.log (adaptedDetRoot P S'.q v) ≤
            Real.log (adaptedDetRoot P S'.q u)) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S
    ServiceAccount P h
      (completed + runTransitionSum (completedStageCharge P l0) run)
      (service + runTransitionSum (serviceTransitionCharge P h) run)
      (runFinalState run) ∧ (runFinalState run).cursor ≤ run.queryScale := by
  induction fuel generalizing S completed service with
  | zero =>
      have hcursor := cursor_le_selectorStep_readScale P Q a rhoMax rhoDr
        jStar h chop l0 H etaReady etaPre deltaShort deltaTerm completed service
        S hh haccount
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next Sn =>
          constructor
          · simpa [runCapped, hout, runTransitionSum, pairedTransitionSum,
              runFinalState] using haccount
          · simpa [runCapped, hout, runFinalState] using hcursor
      | terminal T =>
          have hrule := selectorStep_terminal_rule P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          subst T
          constructor
          · simpa [runCapped, hout, hrule, runTransitionSum,
              pairedTransitionSum, runFinalState, completedStageCharge,
              serviceTransitionCharge] using haccount
          · simpa [runCapped, hout, runFinalState] using hcursor
  | succ fuel ih =>
      have hcursor := cursor_le_selectorStep_readScale P Q a rhoMax rhoDr
        jStar h chop l0 H etaReady etaPre deltaShort deltaTerm completed service
        S hh haccount
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal T =>
          have hrule := selectorStep_terminal_rule P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          have hstate := selectorStep_terminal_state P Q a rhoMax rhoDr jStar h
            chop l0 H etaReady etaPre deltaShort deltaTerm S T hout
          subst T
          constructor
          · simpa [runCapped, hout, hrule, runTransitionSum,
              pairedTransitionSum, runFinalState, completedStageCharge,
              serviceTransitionCharge] using haccount
          · simpa [runCapped, hout, runFinalState] using hcursor
      | next Sn =>
          have hstepMono : ∀ u v : ℤ, S.base ≤ u → u ≤ v →
              v ≤ (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                etaPre deltaShort deltaTerm S).readScale →
                Real.log (adaptedDetRoot P S.q v) ≤
                  Real.log (adaptedDetRoot P S.q u) := by
            intro u v hbase huv hv
            apply hmono S
            · simp [runCapped, hout]
            · exact hbase
            · exact huv
            · have hread :
                  (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                    etaPre deltaShort deltaTerm S).readScale ≤
                    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                      etaPre deltaShort deltaTerm (fuel + 1) S).queryScale := by
                  simp [runCapped, hout]
              exact hv.trans hread
          have hnext := selectorStep_next_serviceAccount P Q a rhoMax rhoDr
            jStar h chop l0 H etaReady etaPre deltaShort deltaTerm completed
            service S Sn hh haccount hstepMono hout
          have htailMono :
              let tail := runCapped P Q a rhoMax rhoDr jStar h chop l0 H
                etaReady etaPre deltaShort deltaTerm fuel Sn
              ∀ S' ∈ tail.states, ∀ u v : ℤ, S'.base ≤ u → u ≤ v →
                v ≤ tail.queryScale →
                  Real.log (adaptedDetRoot P S'.q v) ≤
                    Real.log (adaptedDetRoot P S'.q u) := by
            dsimp only
            intro S' hmem u v hbase huv hv
            apply hmono S'
            · simp only [runCapped, hout, List.mem_cons]
              exact Or.inr hmem
            · exact hbase
            · exact huv
            · have htailQuery :
                  (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                    etaPre deltaShort deltaTerm fuel Sn).queryScale ≤
                    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                      etaPre deltaShort deltaTerm (fuel + 1) S).queryScale := by
                  simp [runCapped, hout]
              exact hv.trans htailQuery
          have htail := ih
            (completed := completed + completedStageCharge P l0 S
              (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                etaPre deltaShort deltaTerm S).rule)
            (service := service + serviceTransitionCharge P h S
              (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                etaPre deltaShort deltaTerm S).rule)
            (S := Sn) hnext htailMono
          constructor
          · simpa only [runCapped, hout, runTransitionSum,
              pairedTransitionSum, add_assoc] using htail.1
          · simp only [runCapped, hout]
            exact htail.2.trans (le_max_right _ _)

private theorem runFinalState_mem
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S : State d) :
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

/-- On an initialized actual run, synchronized service charges have
multiplicity at most the service length against the determinant prefix. -/
theorem runCapped_initial_serviceChargeSum_le_prefixLoss
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h r0 : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (hh : 1 ≤ h) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
    (∀ S' ∈ run.states, ∀ u : ℤ, S'.base ≤ u → u ≤ run.queryScale →
      Book.Ch02.BlockPosDef (adaptedMean P S'.q u)) →
    (∀ S' ∈ run.states, ∀ u v : ℤ, S'.base ≤ u → u ≤ v →
      v ≤ run.queryScale →
        BlockMatLoewnerLE (adaptedMean P S'.q v)
          (adaptedMean P S'.q u)) →
    runTransitionSum (serviceTransitionCharge P h) run ≤
      (h : ℝ) * (runFinalState run).prefixLoss := by
  dsimp only
  intro hpos hmean
  let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
    deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
  have hlog : ∀ S' ∈ run.states, ∀ u v : ℤ, S'.base ≤ u → u ≤ v →
      v ≤ run.queryScale → Real.log (adaptedDetRoot P S'.q v) ≤
        Real.log (adaptedDetRoot P S'.q u) := by
    intro S' hmem u v hbase huv hv
    have hloss := detLoss_nonneg_of_meanOrder
      (hpos S' hmem u hbase (huv.trans hv))
      (hpos S' hmem v (hbase.trans huv) hv)
      (hmean S' hmem u v hbase huv hv)
    rw [detLoss] at hloss
    linarith only [hloss]
  have hinit : ServiceAccount P h 0 0 (initialState r0 A0 hcen hnl) := by
    simp [ServiceAccount, initialState]
  have haccount := runCapped_serviceAccount P Q a rhoMax rhoDr jStar h chop l0
    H fuel etaReady etaPre deltaShort deltaTerm 0 0
    (initialState r0 A0 hcen hnl) hh hinit hlog
  have hdecomp := runCapped_initial_stage_decomposition P Q a rhoMax rhoDr
    jStar h r0 chop l0 H fuel etaReady etaPre deltaShort deltaTerm A0 hcen hnl
  have hmem : runFinalState run ∈ run.states := by
    exact runFinalState_mem P Q a rhoMax rhoDr jStar h chop l0 H fuel etaReady
      etaPre deltaShort deltaTerm (initialState r0 A0 hcen hnl)
  have haccount' : ServiceAccount P h
      (runTransitionSum (completedStageCharge P l0) run)
      (runTransitionSum (serviceTransitionCharge P h) run)
      (runFinalState run) := by
    simpa only [zero_add] using haccount.1
  change runTransitionSum (completedStageCharge P l0) run +
      detLoss P (runFinalState run).q (runFinalState run).base
        (runFinalState run).cursor = (runFinalState run).prefixLoss at hdecomp
  cases hphase : (runFinalState run).phase with
  | fresh | terminal =>
      rw [serviceAccount_eq, hphase] at haccount'
      rw [haccount'.2, detLoss_self, add_zero] at hdecomp
      rw [← hdecomp]
      exact haccount'.1
  | search =>
      rw [serviceAccount_eq, hphase] at haccount'
      have hlower := mul_log_le_detRootWindow hh haccount'.2
        (fun j hj hj' => hlog (runFinalState run) hmem j
          (runFinalState run).cursor hj hj' haccount.2)
      rw [← hdecomp]
      rw [detLoss]
      linarith only [haccount'.1, hlower]

/-- The full actual transition charge is bounded by `h + 2` copies of the
determinant prefix. -/
theorem runCapped_initial_transitionCharge_le_mul_prefixLoss
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h r0 : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (hh : 1 ≤ h) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
    (∀ S' ∈ run.states, ∀ u : ℤ, S'.base ≤ u → u ≤ run.queryScale →
      Book.Ch02.BlockPosDef (adaptedMean P S'.q u)) →
    (∀ S' ∈ run.states, ∀ u v : ℤ, S'.base ≤ u → u ≤ v →
      v ≤ run.queryScale →
        BlockMatLoewnerLE (adaptedMean P S'.q v)
          (adaptedMean P S'.q u)) →
    runTransitionSum (transitionCharge P h l0 H) run ≤
      ((h : ℝ) + 2) * (runFinalState run).prefixLoss := by
  dsimp only
  intro hpos hmean
  let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
    deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
  have hservice := runCapped_initial_serviceChargeSum_le_prefixLoss P Q a
    rhoMax rhoDr jStar h r0 chop l0 H fuel etaReady etaPre deltaShort
    deltaTerm A0 hcen hnl hh hpos hmean
  have hmem : runFinalState run ∈ run.states := by
    exact runFinalState_mem P Q a rhoMax rhoDr jStar h chop l0 H fuel etaReady
      etaPre deltaShort deltaTerm (initialState r0 A0 hcen hnl)
  have hlog : ∀ S' ∈ run.states, ∀ u v : ℤ, S'.base ≤ u → u ≤ v →
      v ≤ run.queryScale → Real.log (adaptedDetRoot P S'.q v) ≤
        Real.log (adaptedDetRoot P S'.q u) := by
    intro S' hS' u v hbase huv hv
    have hloss := detLoss_nonneg_of_meanOrder
      (hpos S' hS' u hbase (huv.trans hv))
      (hpos S' hS' v (hbase.trans huv) hv)
      (hmean S' hS' u v hbase huv hv)
    rw [detLoss] at hloss
    linarith only [hloss]
  have haccount := runCapped_serviceAccount P Q a rhoMax rhoDr jStar h chop l0
    H fuel etaReady etaPre deltaShort deltaTerm 0 0
    (initialState r0 A0 hcen hnl) hh (by simp [ServiceAccount, initialState])
    hlog
  have haccount' : ServiceAccount P h
      (runTransitionSum (completedStageCharge P l0) run)
      (runTransitionSum (serviceTransitionCharge P h) run)
      (runFinalState run) := by
    simpa only [zero_add] using haccount.1
  have hbaseCursor : (runFinalState run).base ≤ (runFinalState run).cursor := by
    cases hphase : (runFinalState run).phase <;>
      rw [serviceAccount_eq, hphase] at haccount'
    · exact haccount'.2.le
    · omega
    · exact haccount'.2.le
  have hcharge := runCapped_initial_transitionCharge_le P Q a rhoMax rhoDr
    jStar h r0 chop l0 H fuel etaReady etaPre deltaShort deltaTerm A0 hcen hnl
    (hpos (runFinalState run) hmem _ le_rfl
      (hbaseCursor.trans haccount.2))
    (hpos (runFinalState run) hmem _ hbaseCursor haccount.2)
    (hmean (runFinalState run) hmem _ _ le_rfl hbaseCursor haccount.2)
  linarith only [hservice, hcharge]

end

end Selection
end HighContrast
end Homogenization
