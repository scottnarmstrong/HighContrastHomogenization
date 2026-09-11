/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchServiceCases
import HCPoly.Provider.Selection.TransitionTrace

/-!
# Read and profile data along selector traces

Actual adjacency supplies the query budget for its read.  Exact checkpoint
data and the portable-history provider also make the current profile finite.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The base of an actual nonterminal successor is among the scales read by
the step that produces it. -/
theorem selectorStep_next_base_le_readScale
    {P : Measure (CoeffSpace d)} {Q a rhoMax rhoDr : ℝ}
    {jStar h : ℤ} {chop : ℝ} {l0 H : ℕ}
    {etaReady etaPre deltaShort deltaTerm : ℝ} {S S' : State d}
    (hh : 0 ≤ h) (hbase : S.base ≤ S.cursor)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm S).outcome = StepOutcome.next S') :
    S'.base ≤
      (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm S).readScale := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;>
    simp [selectorStep, hrule] at hout ⊢
  all_goals subst S'
  all_goals simp [advanceCursor, hopState]
  all_goals omega

/-- The read of a recorded nonterminal step lies below the query scale of the
whole capped run. -/
theorem runCapped_consecutive_readScale_le
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (fuel : ℕ) (S : State d)
    {i : ℕ} {S₀ S₁ : State d}
    (h₀ : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states[i]? = some S₀)
    (h₁ : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states[i + 1]? = some S₁) :
    (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S₀).readScale ≤
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).queryScale := by
  induction fuel generalizing S i S₀ S₁ with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;>
        cases i <;> simp [runCapped, hout] at h₁
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state => cases i <;> simp [runCapped, hout] at h₁
      | next Sn =>
          cases i with
          | zero =>
              simp [runCapped, hout] at h₀
              subst S₀
              simp only [runCapped, hout]
              exact le_max_left
                (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                  etaPre deltaShort deltaTerm S).readScale
                (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                  etaPre deltaShort deltaTerm fuel Sn).queryScale
          | succ i =>
              simp only [runCapped, hout, List.getElem?_cons_succ] at h₀ h₁ ⊢
              exact (ih Sn h₀ h₁).trans (le_max_right _ _)

/-- A finite retained history makes the current portable profile finite at
every defined fixed-grid read. -/
theorem stateProfile_ne_top_of_history
    (hetaProfBar : etaProfBar ≤ 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar TMax : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hhistory : stateHistory S ≤ ENNReal.ofReal c.etaIn)
    (hread : FixedGridReadData (g := g) P jStar S TMax)
    (hcursor : S.cursor ≤ TMax) :
    stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤ := by
  rcases hexact with ⟨-, -, hcentered, hnonlinear, hjcheck, hcheckCursor⟩
  obtain ⟨-, -, -, hbaseProfile, -, -, -, -, hprop⟩ :=
    c.portableData.law P inferInstance hstat hunit jStar S.q hread.rounded
      jStar S.checkpoint TMax le_rfl hjcheck (hcheckCursor.trans hcursor) hread.finiteMean
      hread.positiveMean hread.finiteMoment
  have hhistoryEq : stateHistory S = portableHistory P (initExpQ d g : ℝ)
      (initExpA g) (initExpRhoMax d g) S.q jStar S.checkpoint := by
    rw [stateHistory, portableHistory, hcentered, hnonlinear]
  have hetaIn : c.etaIn ≤ 1 := by
    calc
      c.etaIn ≤ max (max c.etaIn c.etaOut) c.epsSt :=
        (le_max_left _ _).trans (le_max_left _ _)
      _ ≤ etaProfBar := c.profile_caps
      _ ≤ 1 := hetaProfBar
  have hhistoryOne : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.checkpoint ≤ 1 := by
    rw [← hhistoryEq]
    exact hhistory.trans (by simpa using ENNReal.ofReal_le_ofReal hetaIn)
  have hhistoryTop : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.checkpoint ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hhistoryOne
  by_cases hsame : S.checkpoint = S.cursor
  · rw [stateProfile, ← hsame, hbaseProfile]
    exact hhistoryTop
  · have hL : 1 ≤ S.cursor - S.checkpoint := by omega
    have hbound := hprop (S.cursor - S.checkpoint) hL (by omega) hhistoryOne
    have hrhs : ENNReal.ofReal (c.AL (S.cursor - S.checkpoint)) *
          portableHistory P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) S.q jStar S.checkpoint +
        ENNReal.ofReal (c.AL (S.cursor - S.checkpoint) *
          (Real.exp ((initExpQ d g : ℝ) * detIncrement P S.q S.checkpoint
            (S.checkpoint + (S.cursor - S.checkpoint))) - 1)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hhistoryTop,
          ENNReal.ofReal_ne_top⟩
    apply ne_top_of_le_ne_top hrhs
    have heq : S.checkpoint + (S.cursor - S.checkpoint) = S.cursor := by omega
    simpa only [stateProfile, heq] using hbound

end

end Homogenization.HighContrast.Selection
