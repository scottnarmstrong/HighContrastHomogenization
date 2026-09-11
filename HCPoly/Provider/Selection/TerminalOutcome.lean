/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TransitionTrace

/-!
# The terminal rule reached by a capped selector run

A terminal outcome can only arise from T7.  Consequently its state satisfies
the strict complement of the failed terminal determinant test.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Every terminal outcome of a capped run satisfies the T7 guard at the
returned state. -/
theorem runCapped_terminal_guard
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ)
    (S T : State d)
    (hout : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).outcome = RunOutcome.terminal T) :
    ruleGuard P Q a rhoMax rhoDr jStar etaReady etaPre deltaShort deltaTerm
      l0 H .t7 T := by
  induction fuel generalizing S with
  | zero =>
      cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
          deltaShort deltaTerm l0 H S <;>
        simp [runCapped, selectorStep, hrule] at hout
      subst T
      simpa [hrule] using selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
  | succ fuel ih =>
      cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
          deltaShort deltaTerm l0 H S <;>
        simp [runCapped, selectorStep, hrule] at hout
      · exact ih _ hout
      · exact ih _ hout
      · exact ih _ hout
      · exact ih _ hout
      · exact ih _ hout
      · exact ih _ hout
      · subst T
        simpa [hrule] using selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
          etaPre deltaShort deltaTerm l0 H S

/-- A terminal run outcome supplies the strict determinant test used by the
terminal analytic estimates. -/
theorem runCapped_terminal_detRoot_pass
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ)
    (S T : State d)
    (hout : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).outcome = RunOutcome.terminal T)
    (hroot : 0 < adaptedDetRoot P T.q (T.base + (H : ℤ))) :
    adaptedDetRoot P T.q T.base <
      (1 + deltaTerm) * adaptedDetRoot P T.q (T.base + (H : ℤ)) := by
  have hguard := runCapped_terminal_guard P Q a rhoMax rhoDr jStar h chop l0 H
    etaReady etaPre deltaShort deltaTerm fuel S T hout
  exact (terminalTest_passes_iff P deltaTerm H T hroot).mp hguard.2

end

end Homogenization.HighContrast.Selection
