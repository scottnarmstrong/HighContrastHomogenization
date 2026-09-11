/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchFixed
import HCPoly.Provider.Selection.Charges

/-!
# Service branches of the selector

The portable fixed-grid read supplies positivity, mean order, and synchronized
determinant charge on an actual service interval.  Calm and noncalm cases then
give the four scalar rows for T2 and T3.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- An actual service read supplies full positivity and mean order together
with nonnegative ordinary and synchronized determinant charges. -/
theorem serviceIntervalData {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hstart : S.checkpoint + c.h ≤ S.cursor) :
    (∀ j : ℤ, jStar ≤ j → j ≤ S.cursor + c.h →
        (toFullBlockMat (adaptedMean P S.q j)).PosDef) ∧
      (∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ S.cursor + c.h →
        toFullBlockMat (adaptedMean P S.q t) ≤
          toFullBlockMat (adaptedMean P S.q s)) ∧
      0 ≤ detLoss P S.q S.cursor (S.cursor + c.h) ∧
      0 ≤ serviceWindowCharge P S.q c.h S.cursor := by
  rcases hexact with ⟨-, -, -, -, hjcheck, hcheckCursor⟩
  have hh := c.one_le_h
  obtain ⟨hmono, -, -, -, -, -, -, -, -⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hread.rounded
      jStar S.checkpoint (S.cursor + c.h) le_rfl hjcheck
      (hcheckCursor.trans (by omega)) hread.finiteMean hread.positiveMean
      hread.finiteMoment
  have hpos : ∀ j : ℤ, jStar ≤ j → j ≤ S.cursor + c.h →
      (toFullBlockMat (adaptedMean P S.q j)).PosDef := by
    intro j hj hjv
    exact posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q j)
      (hread.positiveMean j hj hjv)
  have hfull : ∀ s t : ℤ, jStar ≤ s → s ≤ t →
      t ≤ S.cursor + c.h →
      toFullBlockMat (adaptedMean P S.q t) ≤
        toFullBlockMat (adaptedMean P S.q s) := by
    intro s t hjs hst htv
    exact le_of_blockMatLoewnerLE
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t)
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q s)
      (hmono s t hjs hst htv)
  have hloss : 0 ≤ detLoss P S.q S.cursor (S.cursor + c.h) :=
    detLoss_nonneg_of_meanOrder
      (hread.positiveMean S.cursor (hjcheck.trans hcheckCursor) (by omega))
      (hread.positiveMean (S.cursor + c.h)
        ((hjcheck.trans hcheckCursor).trans (by omega)) le_rfl)
      (hmono S.cursor (S.cursor + c.h) (hjcheck.trans hcheckCursor)
        (by omega) le_rfl)
  have hservice : 0 ≤ serviceWindowCharge P S.q c.h S.cursor := by
    rw [serviceWindowCharge_eq]
    exact Finset.sum_nonneg fun j hj => by
      have hjb := Finset.mem_Icc.mp hj
      exact detLoss_nonneg_of_meanOrder
        (hread.positiveMean (j - c.h) (by omega) (by omega))
        (hread.positiveMean j (by omega) (by omega))
        (hmono (j - c.h) j (by omega) (by omega) (by omega))
  exact ⟨hpos, hfull, hloss, hservice⟩

/-- Work and drift-index increments give the corresponding potential increment
on a same-grid search update. -/
theorem servicePotentialChange_le {P : Measure (CoeffSpace d)}
    {jStar : ℤ} {S : State d} {A B : ℝ}
    (hphase : S.phase = Phase.search)
    (hwork : c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar
          (advanceCursor P S (S.cursor + c.h) .search none) ≤
      c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar S + A)
    (hdrift : (driftIndex P (initExpRhoDr g) c.etaPre jStar
        (advanceCursor P S (S.cursor + c.h) .search none) : ℝ) ≤
      (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) + B)
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch
            (advanceCursor P S (S.cursor + c.h) .search none) -
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S ≤ A + B := by
  rw [w.alphaW_eq]
  simp [statePotential, stateProjectiveDistance, advanceCursor, hphase] at ⊢
  simp only [advanceCursor] at hwork
  simp only [driftIndex, advanceCursor] at hdrift
  simp only [driftIndex] at ⊢
  linarith only [hwork, hdrift]

/-- The selected projective weight dominates both service-branch determinant
slopes. -/
theorem serviceSlopes_le_weight
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) ≤ c.Cdir * w.alphaX ∧
      (d : ℝ) / Real.log 2 ≤ c.Cdir * w.alphaX := by
  have hs := directionalSlope_bounds (c := c)
  have hCdir : 0 ≤ c.Cdir :=
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hs.1
  have hweight : c.Cdir ≤ c.Cdir * w.alphaX := by
    have := mul_le_mul_of_nonneg_left
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) w.two_le_alphaX) hCdir
    simpa only [mul_one] using this
  exact ⟨hs.2.1.trans hweight, hs.2.2.trans hweight⟩

/-- A noncalm determinant ratio strictly exceeds the common expensive-branch
charge scale. -/
theorem serviceNoncalmScale {P : Measure (CoeffSpace d)}
    {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hratio : c.rDr < adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + c.h)) :
    potentialScale c < detLoss P S.q S.cursor (S.cursor + c.h) := by
  have hjcursor := hexact.2.2.2.2.1.trans hexact.2.2.2.2.2
  have hh := c.one_le_h
  have hu := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.cursor)
    (hread.positiveMean S.cursor hjcursor (by omega))
  have hv := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q (S.cursor + c.h))
    (hread.positiveMean _ (hjcursor.trans (by omega)) le_rfl)
  have hlog := Real.strictMonoOn_log (lt_trans zero_lt_one c.one_lt_rDr)
    (div_pos (ShortHop.detRoot_pos hu) (ShortHop.detRoot_pos hv)) hratio
  have hlogeq : Real.log (adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + c.h)) =
      detLoss P S.q S.cursor (S.cursor + c.h) :=
    log_adaptedDetRoot_div_eq_detLoss hu hv
  change Real.log c.rDr < Real.log
    (adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + c.h)) at hlog
  rw [hlogeq] at hlog
  exact lt_of_le_of_lt (by rw [potentialScale_eq]; exact min_le_left _ _) hlog

/-- A calm T2 service update decreases the positive drift index by one. -/
theorem branchT2CalmRow (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H .t2 S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hprofileFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤)
    (hratio : adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + c.h) ≤ c.rDr)
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    PotentialRow w .t2
      (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch
          (advanceCursor P S (S.cursor + c.h) .search none) -
       statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S)
      (transitionCharge P c.h c.l0 H S .t2) := by
  rcases hsearch with ⟨hphase, hstart, -⟩
  rcases hguard with ⟨-, hdriftPos⟩
  obtain ⟨hpos, hmono, hloss, hservice⟩ :=
    serviceIntervalData (c := c) hP hunit hexact hread hstart
  have hcalm := driftIndex_calm hd (initExpRhoDr_pos hg).le c.etaPre_pos S
    (hexact.2.2.2.2.1.trans hexact.2.2.2.2.2) c.one_le_h
    c.drift_service_le hratio c.rDr_pow_le c.rDr_drift hpos hmono
  have hwork := serviceWork_le (c := c) hd hP hunit hexact hread hstart
    hprofileFinite
  have hdriftNat := hcalm.1 hdriftPos
  have hdriftReal : (driftIndex P (initExpRhoDr g) c.etaPre jStar
        (advanceCursor P S (S.cursor + c.h) .search none) : ℝ) ≤
      (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) - 1 := by
    have : driftIndex P (initExpRhoDr g) c.etaPre jStar
        (advanceCursor P S (S.cursor + c.h) .search none) + 1 ≤
      driftIndex P (initExpRhoDr g) c.etaPre jStar S := by
      simpa only [driftIndex, advanceCursor] using (show
        driftIndex P (initExpRhoDr g) c.etaPre jStar
          {S with cursor := S.cursor + c.h} + 1 ≤
            driftIndex P (initExpRhoDr g) c.etaPre jStar S by omega)
    have hcast :
        ((driftIndex P (initExpRhoDr g) c.etaPre jStar
          (advanceCursor P S (S.cursor + c.h) .search none) + 1 : ℕ) : ℝ) ≤
          (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) := by
      exact_mod_cast this
    push_cast at hcast
    linarith only [hcast]
  have hraw := servicePotentialChange_le (c := c) hphase hwork hdriftReal w
  apply PotentialRow.t2Calm
  change _ ≤ -1 + c.Cdir * w.alphaX *
    (detLoss P S.q S.cursor (S.cursor + c.h) +
      serviceWindowCharge P S.q c.h S.cursor)
  have hs := serviceSlopes_le_weight w
  have hsvc := mul_le_mul_of_nonneg_right hs.1 hservice
  have hweight0 : 0 ≤ c.Cdir * w.alphaX := by
    have hCphi : 0 ≤ c.Cphi := by
      rw [c.Cphi_eq]
      exact le_trans zero_le_one (le_max_left _ _)
    exact (mul_nonneg (mul_nonneg hCphi (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)).trans hs.1
  have hcharge : c.Cdir * w.alphaX *
        serviceWindowCharge P S.q c.h S.cursor ≤
      c.Cdir * w.alphaX *
        (detLoss P S.q S.cursor (S.cursor + c.h) +
          serviceWindowCharge P S.q c.h S.cursor) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hloss) hweight0
  calc
    _ ≤ c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) *
          serviceWindowCharge P S.q c.h S.cursor + -1 := hraw
    _ ≤ -1 + c.Cdir * w.alphaX *
        (detLoss P S.q S.cursor (S.cursor + c.h) +
          serviceWindowCharge P S.q c.h S.cursor) := by
      linarith only [hsvc, hcharge]

end

end Homogenization.HighContrast.Selection
