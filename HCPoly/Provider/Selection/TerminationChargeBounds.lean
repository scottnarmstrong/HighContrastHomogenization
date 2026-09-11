/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TerminationCharges

/-!
# Bounds from exact selector charge accounting

Mean order makes the final partial-stage loss nonnegative.  The exact trace
identities then show that completed-stage summaries cost at most one prefix
and that all non-service pieces of the transition charge cost at most two.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Mean order at the final reached state leaves at most one determinant
prefix for all completed T5 stage summaries. -/
theorem runCapped_initial_completedStageChargeSum_le_prefixLoss
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h r0 : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
    Book.Ch02.BlockPosDef
        (adaptedMean P (runFinalState run).q (runFinalState run).base) →
      Book.Ch02.BlockPosDef
        (adaptedMean P (runFinalState run).q (runFinalState run).cursor) →
      BlockMatLoewnerLE
          (adaptedMean P (runFinalState run).q (runFinalState run).cursor)
          (adaptedMean P (runFinalState run).q (runFinalState run).base) →
      runTransitionSum (completedStageCharge P l0) run ≤
        (runFinalState run).prefixLoss := by
  dsimp only
  intro hbase hcursor hmono
  have hcurrent : 0 ≤
      detLoss P
        (runFinalState (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
          etaPre deltaShort deltaTerm fuel
          (initialState r0 A0 hcen hnl))).q
        (runFinalState (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
          etaPre deltaShort deltaTerm fuel
          (initialState r0 A0 hcen hnl))).base
        (runFinalState (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
          etaPre deltaShort deltaTerm fuel
          (initialState r0 A0 hcen hnl))).cursor :=
    detLoss_nonneg_of_meanOrder hbase hcursor hmono
  have hdecomp := runCapped_initial_stage_decomposition P Q a rhoMax rhoDr
    jStar h r0 chop l0 H fuel etaReady etaPre deltaShort deltaTerm A0 hcen hnl
  linarith only [hdecomp, hcurrent]

/-- After mean order controls the final partial stage, the full actual trace
charge is at most two copies of the determinant prefix plus its synchronized
service terms. -/
theorem runCapped_initial_transitionCharge_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h r0 : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) :
    let run := runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel (initialState r0 A0 hcen hnl)
    Book.Ch02.BlockPosDef
        (adaptedMean P (runFinalState run).q (runFinalState run).base) →
      Book.Ch02.BlockPosDef
        (adaptedMean P (runFinalState run).q (runFinalState run).cursor) →
      BlockMatLoewnerLE
          (adaptedMean P (runFinalState run).q (runFinalState run).cursor)
          (adaptedMean P (runFinalState run).q (runFinalState run).base) →
      runTransitionSum (transitionCharge P h l0 H) run ≤
        2 * (runFinalState run).prefixLoss +
          runTransitionSum (serviceTransitionCharge P h) run := by
  dsimp only
  intro hbase hcursor hmono
  have hcompleted := runCapped_initial_completedStageChargeSum_le_prefixLoss
    P Q a rhoMax rhoDr jStar h r0 chop l0 H fuel etaReady etaPre deltaShort
      deltaTerm A0 hcen hnl hbase hcursor hmono
  have hordinary := runCapped_initial_ordinaryChargeSum_eq P Q a rhoMax rhoDr
    jStar h r0 chop l0 H fuel etaReady etaPre deltaShort deltaTerm A0 hcen hnl
  have hsplit := runTransitionSum_transitionCharge_eq P h l0 H
    (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre deltaShort
      deltaTerm fuel (initialState r0 A0 hcen hnl))
  linarith only [hcompleted, hordinary, hsplit]

end

end Selection
end HighContrast
end Homogenization
