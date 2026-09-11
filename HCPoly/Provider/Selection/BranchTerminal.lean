/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchFixed
import HCPoly.Provider.Selection.BranchWork
import HCPoly.Provider.Selection.Charges

/-!
# Failed terminal-test branch

The failed terminal test is extended to the full read span by fixed-grid mean
order.  Its actual cursor update then supplies the terminal scalar row.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The actual T6 update supplies the failed-terminal-test scalar row, with
the test charge extended to the full `max H h` read interval. -/
theorem branchT6Row (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hetaProfBar : etaProfBar ≤ 1) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hterminal : TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew
      c.etaX jStar S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H .t6 S)
    (hread : FixedGridReadData (g := g) P jStar S
      (S.base + max (H : ℤ) c.h))
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    PotentialRow w .t6
      (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch
          (advanceCursor P S (S.base + max (H : ℤ) c.h) .search none) -
       statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S)
      (transitionCharge P c.h c.l0 H S .t6) := by
  rcases hterminal with
    ⟨hphase, hbase, hcheckpoint, hhistory, -, -⟩
  rcases hguard with ⟨-, hfail⟩
  rcases hexact with ⟨hq, hmean, hcentered, hnonlinear, hjcheck, hcheckCursor⟩
  have hbaseCursor : S.base = S.cursor := hbase.trans hcheckpoint
  have hcursorTarget : S.cursor ≤ S.cursor + max (H : ℤ) c.h := by
    have : (1 : ℤ) ≤ max (H : ℤ) c.h :=
      c.one_le_h.trans (le_max_right _ _)
    omega
  have hreadCursor : FixedGridReadData (g := g) P jStar S
      (S.cursor + max (H : ℤ) c.h) := by
    simpa only [hbaseCursor] using hread
  have hL : (1 : ℤ) ≤ max (H : ℤ) c.h :=
    c.one_le_h.trans (le_max_right _ _)
  have hexact' : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S :=
    ⟨hq, hmean, hcentered, hnonlinear, hjcheck, hcheckCursor⟩
  have hwork := startupWork_le (c := c) hd hetaProfBar hP hunit hL hexact'
    hreadCursor hcheckpoint hhistory
  have hb := fixedAdvanceBounds (c := c) hd hg hP hunit hexact' hreadCursor
    hcursorTarget
  have hdrift := hb.1
  have hwork0 := mul_nonneg c.etaReady_pos.le
    (stateWork_nonneg c.etaReady_pos
      (P := P) (Q := (initExpQ d g : ℝ)) (a := initExpA g)
      (rhoMax := initExpRhoMax d g) (jStar := jStar) (S := S))
  have hbHop : 0 ≤ (c.bHop : ℝ) := Nat.cast_nonneg _
  obtain ⟨hmono, -, -, -, -, -, -, -, -⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hreadCursor.rounded
      jStar S.checkpoint (S.cursor + max (H : ℤ) c.h) le_rfl hjcheck
      (hcheckCursor.trans hcursorTarget) hreadCursor.finiteMean
      hreadCursor.positiveMean hreadCursor.finiteMoment
  have hjcursor : jStar ≤ S.cursor := hjcheck.trans hcheckCursor
  have hHtarget : S.cursor + (H : ℤ) ≤ S.cursor + max (H : ℤ) c.h := by
    omega
  have hbasePos := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.cursor)
    (hreadCursor.positiveMean S.cursor hjcursor hcursorTarget)
  have hHPos := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q (S.cursor + (H : ℤ)))
    (hreadCursor.positiveMean _ (hjcursor.trans (by omega)) hHtarget)
  have htargetPos := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q
      (S.cursor + max (H : ℤ) c.h))
    (hreadCursor.positiveMean _ (hjcursor.trans hcursorTarget) le_rfl)
  have hrootOrder :
      adaptedDetRoot P S.q (S.cursor + max (H : ℤ) c.h) ≤
        adaptedDetRoot P S.q (S.cursor + (H : ℤ)) := by
    exact ShortHop.detRoot_le_of_blockMatLoewnerLE htargetPos hHPos
      (le_of_blockMatLoewnerLE
        (Recurrence.isSymmetricBlockMat_adaptedMean P S.q
          (S.cursor + max (H : ℤ) c.h))
        (Recurrence.isSymmetricBlockMat_adaptedMean P S.q (S.cursor + (H : ℤ)))
        (hmono (S.cursor + (H : ℤ))
          (S.cursor + max (H : ℤ) c.h) (hjcursor.trans (by omega))
          hHtarget le_rfl))
  have hratioExtend :
      adaptedDetRoot P S.q S.cursor /
          adaptedDetRoot P S.q (S.cursor + (H : ℤ)) ≤
        adaptedDetRoot P S.q S.cursor /
          adaptedDetRoot P S.q (S.cursor + max (H : ℤ) c.h) := by
    exact div_le_div_of_nonneg_left (ShortHop.detRoot_pos hbasePos).le
      (ShortHop.detRoot_pos htargetPos) hrootOrder
  have hfailCursor : 1 + c.deltaTerm ≤
      adaptedDetRoot P S.q S.cursor /
        adaptedDetRoot P S.q (S.cursor + (H : ℤ)) := by
    change 1 + c.deltaTerm ≤
      adaptedDetRoot P S.q S.base /
        adaptedDetRoot P S.q (S.base + (H : ℤ)) at hfail
    simpa only [hbaseCursor] using hfail
  have hratio : 1 + c.deltaTerm ≤
      adaptedDetRoot P S.q S.cursor /
        adaptedDetRoot P S.q (S.cursor + max (H : ℤ) c.h) :=
    hfailCursor.trans hratioExtend
  have hterm : Real.log (1 + c.deltaTerm) ≤
      detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) := by
    have hlog := Real.log_le_log
      (add_pos_of_pos_of_nonneg zero_lt_one c.deltaTerm_pos.le) hratio
    have hlogeq :
        Real.log
            (detRoot d (adaptedMean P S.q S.cursor) /
              detRoot d (adaptedMean P S.q
                (S.cursor + max (H : ℤ) c.h))) =
          detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) :=
      log_adaptedDetRoot_div_eq_detLoss hbasePos htargetPos
    change Real.log (1 + c.deltaTerm) ≤
      Real.log (detRoot d (adaptedMean P S.q S.cursor) /
        detRoot d (adaptedMean P S.q
          (S.cursor + max (H : ℤ) c.h))) at hlog
    rw [hlogeq] at hlog
    exact hlog
  have hrawCursor :
      statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch
            (advanceCursor P S (S.cursor + max (H : ℤ) c.h) .search none) -
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S ≤
      (fixedSpanLoad (c.AL (max (H : ℤ) c.h)) +
          driftIndexLoad d c.etaPre + (c.bHop : ℝ)) +
        ((initExpQ d g : ℝ) * (d : ℝ) + (d : ℝ) / Real.log 2) *
          detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) +
        w.alphaSearch := by
    rw [w.alphaW_eq]
    simp [statePotential, stateProjectiveDistance, advanceCursor, hphase] at ⊢
    simp only [advanceCursor] at hwork
    rw [add_mul]
    have hsum := add_le_add hwork hdrift
    simp only [driftIndex] at hsum ⊢
    linarith only [hsum, hwork0, hbHop]
  have hraw :
      statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch
            (advanceCursor P S (S.base + max (H : ℤ) c.h) .search none) -
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S ≤
      terminalFailureBranchLoad c + fixedBranchSlope d g *
          detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) +
        w.alphaSearch := by
    simpa only [hbaseCursor, terminalFailureBranchLoad_eq,
      fixedBranchSlope_eq] using hrawCursor
  apply PotentialRow.t6
  · change Real.log (1 + c.deltaTerm) ≤
      detLoss P S.q S.base (S.base + max (H : ℤ) c.h)
    simpa only [hbaseCursor] using hterm
  · change
      statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
              w.alphaFresh w.alphaSearch
              (advanceCursor P S (S.base + max (H : ℤ) c.h) .search none) -
          statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
              w.alphaFresh w.alphaSearch S ≤
        potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
            (terminalFailureBranchLoad c) + hopBranchLoad c + w.c0 +
          w.alphaX * (projectiveError c.etaX + hopFeedback c) +
          c.Cdir * w.alphaX *
            detLoss P S.q S.base (S.base + max (H : ℤ) c.h)
    have hload : terminalFailureBranchLoad c ≤ potentialLoad c
        (startupBranchLoad c) (shortFailureBranchLoad c)
          (terminalFailureBranchLoad c) :=
      (le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    have hslope := mul_le_mul_of_nonneg_right
      (fixedBranchSlope_le_weight w) hb.2
    have hfinal :
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
              (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
                w.alphaFresh w.alphaSearch
                (advanceCursor P S (S.base + max (H : ℤ) c.h) .search none) -
            statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
              (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
                w.alphaFresh w.alphaSearch S ≤
          potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
              (terminalFailureBranchLoad c) + hopBranchLoad c + w.c0 +
            w.alphaX * (projectiveError c.etaX + hopFeedback c) +
            c.Cdir * w.alphaX *
              detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) := by
      calc
      _ ≤ terminalFailureBranchLoad c + fixedBranchSlope d g *
          detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) +
            w.alphaSearch := hraw
      _ ≤ potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
            (terminalFailureBranchLoad c) +
          c.Cdir * w.alphaX *
            detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) +
          w.alphaSearch := add_le_add (add_le_add hload hslope) le_rfl
      _ = potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
            (terminalFailureBranchLoad c) + hopBranchLoad c + w.c0 +
          w.alphaX * (projectiveError c.etaX + hopFeedback c) +
          c.Cdir * w.alphaX *
            detLoss P S.q S.cursor (S.cursor + max (H : ℤ) c.h) := by
        rw [w.alphaSearch_eq]
        ring
    simpa only [hbaseCursor] using hfinal

end

end Homogenization.HighContrast.Selection
