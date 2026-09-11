/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchWork
import HCPoly.Provider.Selection.Charges

/-!
# Fixed-span selector branches

The branch loads retain every span-dependent term.  The accompanying rows are
proved for the actual same-grid state updates of the selector.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal
open scoped MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The common determinant slope of fixed-grid work and drift. -/
def fixedBranchSlope (d : ℕ) (g : ℝ) : ℝ :=
  (initExpQ d g : ℝ) * (d : ℝ) + (d : ℝ) / Real.log 2

/-- Defining equation for the common fixed-grid slope. -/
theorem fixedBranchSlope_eq : fixedBranchSlope d g =
    (initExpQ d g : ℝ) * (d : ℝ) + (d : ℝ) / Real.log 2 := rfl

/-- The fresh-start additive load. -/
def startupBranchLoad (c : Constants d H g epsCal etaDr etaProfBar
    deltaDetBar Cd Khop Ctr Ltr) : ℝ :=
  fixedSpanLoad (c.AL c.h) + driftIndexLoad d c.etaPre + (c.bHop : ℝ)

/-- Defining equation for the fresh-start load. -/
theorem startupBranchLoad_eq : startupBranchLoad c =
    fixedSpanLoad (c.AL c.h) + driftIndexLoad d c.etaPre + (c.bHop : ℝ) := rfl

/-- The failed-short-test additive load. -/
def shortFailureBranchLoad (c : Constants d H g epsCal etaDr etaProfBar
    deltaDetBar Cd Khop Ctr Ltr) : ℝ :=
  fixedSpanLoad (c.AL (2 * (c.l0 : ℤ))) + driftIndexLoad d c.etaPre

/-- Defining equation for the failed-short-test load. -/
theorem shortFailureBranchLoad_eq : shortFailureBranchLoad c =
    fixedSpanLoad (c.AL (2 * (c.l0 : ℤ))) + driftIndexLoad d c.etaPre := rfl

/-- The projective-hop additive load used when the weights are chosen. -/
def hopBranchLoad (c : Constants d H g epsCal etaDr etaProfBar
    deltaDetBar Cd Khop Ctr Ltr) : ℝ :=
  c.etaReady * Real.log (1 + c.etaIn / c.etaReady) + (c.bHop : ℝ)

/-- Defining equation for the projective-hop load. -/
theorem hopBranchLoad_eq : hopBranchLoad c =
    c.etaReady * Real.log (1 + c.etaIn / c.etaReady) + (c.bHop : ℝ) := rfl

/-- The failed-terminal-test additive load. -/
def terminalFailureBranchLoad (c : Constants d H g epsCal etaDr etaProfBar
    deltaDetBar Cd Khop Ctr Ltr) : ℝ :=
  fixedSpanLoad (c.AL (max (H : ℤ) c.h)) + driftIndexLoad d c.etaPre +
    (c.bHop : ℝ)

/-- Defining equation for the failed-terminal-test load. -/
theorem terminalFailureBranchLoad_eq : terminalFailureBranchLoad c =
    fixedSpanLoad (c.AL (max (H : ℤ) c.h)) + driftIndexLoad d c.etaPre +
      (c.bHop : ℝ) := rfl

/-- Mean order on an actual fixed-grid read controls both its drift-index
increment and its normalized determinant loss. -/
theorem fixedAdvanceBounds (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar v : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hread : FixedGridReadData (g := g) P jStar S v) (huv : S.cursor ≤ v) :
    (driftIndex P (initExpRhoDr g) c.etaPre jStar {S with cursor := v} : ℝ) ≤
        (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) +
          driftIndexLoad d c.etaPre +
            (d : ℝ) / Real.log 2 * detLoss P S.q S.cursor v ∧
      0 ≤ detLoss P S.q S.cursor v := by
  rcases hexact with ⟨-, -, -, -, hjcheck, hcheckCursor⟩
  obtain ⟨hmono, -, -, -, -, -, -, -, -⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hread.rounded
      jStar S.checkpoint v le_rfl hjcheck (hcheckCursor.trans huv)
      hread.finiteMean hread.positiveMean hread.finiteMoment
  have hfull : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v →
      toFullBlockMat (adaptedMean P S.q t) ≤
        toFullBlockMat (adaptedMean P S.q s) := by
    intro s t hjs hst htv
    exact le_of_blockMatLoewnerLE
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t)
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q s)
      (hmono s t hjs hst htv)
  have hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v →
      (toFullBlockMat (adaptedMean P S.q j)).PosDef := fun j hj hjv =>
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q j)
      (hread.positiveMean j hj hjv)
  constructor
  · exact driftIndex_general hd (initExpRhoDr_pos hg).le c.etaPre_pos S
      (hjcheck.trans hcheckCursor) huv hpos hfull
  · exact detLoss_nonneg_of_meanOrder
      (hread.positiveMean S.cursor (hjcheck.trans hcheckCursor) huv)
      (hread.positiveMean v (hjcheck.trans (hcheckCursor.trans huv)) le_rfl)
      (hmono S.cursor v (hjcheck.trans hcheckCursor) huv le_rfl)

/-- Two projective-weight units dominate the two fixed-grid determinant
slopes. -/
theorem fixedBranchSlope_le_weight
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    fixedBranchSlope d g ≤ c.Cdir * w.alphaX := by
  have hs := directionalSlope_bounds (c := c)
  have hCdir : 0 ≤ c.Cdir :=
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hs.1
  have htwo := mul_le_mul_of_nonneg_right w.two_le_alphaX hCdir
  have hbound :
      (initExpQ d g : ℝ) * (d : ℝ) + (d : ℝ) / Real.log 2 ≤
        c.Cdir * w.alphaX := by
    calc
    (initExpQ d g : ℝ) * (d : ℝ) + (d : ℝ) / Real.log 2 ≤
        c.Cdir + c.Cdir := add_le_add hs.1 hs.2.2
    _ = 2 * c.Cdir := by ring
    _ ≤ w.alphaX * c.Cdir := by simpa only [mul_comm] using htwo
    _ = c.Cdir * w.alphaX := by ring
  exact hbound

/-- The actual Root update supplies its source scalar row. -/
theorem branchT1Row (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hetaProfBar : etaProfBar ≤ 1) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hfresh : FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    PotentialRow w .t1
      (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch
          (advanceCursor P S (S.cursor + c.h) .search none) -
       statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S)
      (transitionCharge P c.h c.l0 H S .t1) := by
  rcases hfresh with ⟨hphase, -, hcheckpoint, -, hhistory, -⟩
  have hwork := startupWork_le (c := c) hd hetaProfBar hP hunit c.one_le_h
    hexact hread hcheckpoint hhistory
  have hh := c.one_le_h
  have hb := fixedAdvanceBounds (c := c) hd hg hP hunit hexact hread (by omega)
  have hdrift :
      (driftIndex P (initExpRhoDr g) c.etaPre jStar
        (advanceCursor P S (S.cursor + c.h) .search none) : ℝ) ≤
        (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) +
          driftIndexLoad d c.etaPre + (d : ℝ) / Real.log 2 *
            detLoss P S.q S.cursor (S.cursor + c.h) := by
    simpa only [driftIndex, advanceCursor] using hb.1
  have hwork0 := mul_nonneg c.etaReady_pos.le (stateWork_nonneg c.etaReady_pos
    (P := P) (Q := (initExpQ d g : ℝ)) (a := initExpA g)
    (rhoMax := initExpRhoMax d g) (jStar := jStar) (S := S))
  have hbHop : 0 ≤ (c.bHop : ℝ) := Nat.cast_nonneg _
  simp only [advanceCursor] at hwork hdrift
  apply PotentialRow.t1
  simp only [transitionCharge, fixedBranchSlope, startupBranchLoad]
  rw [w.alphaW_eq, w.alphaFresh_eq]
  simp [statePotential, stateProjectiveDistance, advanceCursor, hphase]
  rw [add_mul]
  linarith only [hwork, hdrift, hwork0, hbHop]

/-- The actual T4 update supplies the failed-short-test scalar row. -/
theorem branchT4Row (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H .t4 S)
    (hread : FixedGridReadData (g := g) P jStar S
      (S.cursor + 2 * (c.l0 : ℤ)))
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    PotentialRow w .t4
      (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch
          (advanceCursor P S (S.cursor + 2 * (c.l0 : ℤ)) .search none) -
       statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S)
      (transitionCharge P c.h c.l0 H S .t4) := by
  rcases hsearch with ⟨-, hstart, -⟩
  rcases hguard with ⟨hphase, -, hprofile, hfail⟩
  have hcommon : 1 ≤ c.Lcommon := by rw [c.Lcommon_eq]; omega
  have hl0 : 1 ≤ c.l0 := hcommon.trans
    ((le_max_left c.Lcommon Ltr).trans c.l0_lower)
  have hL : (1 : ℤ) ≤ 2 * (c.l0 : ℤ) := by exact_mod_cast (by omega : 1 ≤ 2 * c.l0)
  have hwork := propagationWork_le (c := c) hd hP hunit hL hexact hread hstart hprofile
  have hb := fixedAdvanceBounds (c := c) hd hg hP hunit hexact hread (by omega)
  have hdrift := hb.1
  have hwork0 := mul_nonneg c.etaReady_pos.le (stateWork_nonneg c.etaReady_pos
    (P := P) (Q := (initExpQ d g : ℝ)) (a := initExpA g)
    (rhoMax := initExpRhoMax d g) (jStar := jStar) (S := S))
  have hu := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.cursor)
    (hread.positiveMean S.cursor
      (hexact.2.2.2.2.1.trans hexact.2.2.2.2.2) (by omega))
  have hv := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q
      (S.cursor + 2 * (c.l0 : ℤ)))
    (hread.positiveMean _
      ((hexact.2.2.2.2.1.trans hexact.2.2.2.2.2).trans (by omega)) le_rfl)
  have hlog : Real.log (1 + c.deltaShort) <
      detLoss P S.q S.cursor (S.cursor + 2 * (c.l0 : ℤ)) := by
    have hr := Real.strictMonoOn_log
      (add_pos_of_pos_of_nonneg zero_lt_one c.deltaShort_pos.le)
      (div_pos (ShortHop.detRoot_pos hu) (ShortHop.detRoot_pos hv)) hfail
    have hlogeq :
        Real.log
            (detRoot d (adaptedMean P S.q S.cursor) /
              detRoot d (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ)))) =
          detLoss P S.q S.cursor (S.cursor + 2 * (c.l0 : ℤ)) :=
      log_adaptedDetRoot_div_eq_detLoss hu hv
    rw [hlogeq] at hr
    exact hr
  have hscale : potentialScale c <
      detLoss P S.q S.cursor (S.cursor + 2 * (c.l0 : ℤ)) := by
    rw [potentialScale_eq]
    exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) hlog
  have hraw :
      statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch
            (advanceCursor P S (S.cursor + 2 * (c.l0 : ℤ)) .search none) -
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S ≤
      shortFailureBranchLoad c + fixedBranchSlope d g *
        detLoss P S.q S.cursor (S.cursor + 2 * (c.l0 : ℤ)) := by
    rw [w.alphaW_eq]
    simp only [shortFailureBranchLoad]
    simp [statePotential, stateProjectiveDistance, advanceCursor, hphase] at ⊢
    simp only [advanceCursor] at hwork
    rw [fixedBranchSlope_eq, add_mul]
    have hsum := add_le_add hwork hdrift
    simp only [driftIndex] at hsum ⊢
    linarith only [hsum, hwork0]
  apply PotentialRow.t4 hscale
  have hload : shortFailureBranchLoad c ≤ potentialLoad c
      (startupBranchLoad c) (shortFailureBranchLoad c) (terminalFailureBranchLoad c) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hslope := mul_le_mul_of_nonneg_right (fixedBranchSlope_le_weight w) hb.2
  exact hraw.trans (add_le_add hload hslope)

end

end Homogenization.HighContrast.Selection
