/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchService

/-!
# Remaining service-branch cases

Above readiness, a calm service step pays the strict work decrement.  When the
determinant ratio is noncalm, the common charge scale pays the fixed drift load
and both determinant slopes.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

private theorem serviceTerm_le_weightedCharge {P : Measure (CoeffSpace d)}
    {S : State d}
    (hloss : 0 ≤ detLoss P S.q S.cursor (S.cursor + c.h))
    (hservice : 0 ≤ serviceWindowCharge P S.q c.h S.cursor)
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) *
        serviceWindowCharge P S.q c.h S.cursor ≤
      c.Cdir * w.alphaX *
        (detLoss P S.q S.cursor (S.cursor + c.h) +
          serviceWindowCharge P S.q c.h S.cursor) := by
  have hs := serviceSlopes_le_weight (c := c) w
  have hsvc := mul_le_mul_of_nonneg_right hs.1 hservice
  have hCphi : 0 ≤ c.Cphi := by
    rw [c.Cphi_eq]
    exact le_trans zero_le_one (le_max_left _ _)
  have hweight0 : 0 ≤ c.Cdir * w.alphaX :=
    (mul_nonneg (mul_nonneg hCphi (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)).trans hs.1
  exact hsvc.trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left hloss) hweight0)

private theorem noncalmServicePotential_le (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hphase : S.phase = Phase.search)
    (hstart : S.checkpoint + c.h ≤ S.cursor)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hprofileFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤)
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch
            (advanceCursor P S (S.cursor + c.h) .search none) -
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S ≤
      potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
          (terminalFailureBranchLoad c) + c.Cdir * w.alphaX *
        (detLoss P S.q S.cursor (S.cursor + c.h) +
          serviceWindowCharge P S.q c.h S.cursor) := by
  obtain ⟨-, -, hloss, hservice⟩ :=
    serviceIntervalData (c := c) hP hunit hexact hread hstart
  have hh := c.one_le_h
  have hwork := serviceWork_le (c := c) hd hP hunit hexact hread hstart
    hprofileFinite
  have hb := fixedAdvanceBounds (c := c) hd hg hP hunit hexact hread (by omega)
  have hdrift : (driftIndex P (initExpRhoDr g) c.etaPre jStar
        (advanceCursor P S (S.cursor + c.h) .search none) : ℝ) ≤
      (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) +
        (driftIndexLoad d c.etaPre + (d : ℝ) / Real.log 2 *
          detLoss P S.q S.cursor (S.cursor + c.h)) := by
    simpa only [driftIndex, advanceCursor, add_assoc] using hb.1
  have hraw := servicePotentialChange_le (c := c) hphase hwork hdrift w
  have hload : driftIndexLoad d c.etaPre ≤ potentialLoad c
      (startupBranchLoad c) (shortFailureBranchLoad c)
        (terminalFailureBranchLoad c) :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hs := serviceSlopes_le_weight (c := c) w
  have hlossBound := mul_le_mul_of_nonneg_right hs.2 hloss
  have hserviceBound := mul_le_mul_of_nonneg_right hs.1 hservice
  calc
    _ ≤ c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) *
          serviceWindowCharge P S.q c.h S.cursor +
        (driftIndexLoad d c.etaPre + (d : ℝ) / Real.log 2 *
          detLoss P S.q S.cursor (S.cursor + c.h)) := hraw
    _ = driftIndexLoad d c.etaPre +
        ((d : ℝ) / Real.log 2 *
          detLoss P S.q S.cursor (S.cursor + c.h) +
         c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) *
          serviceWindowCharge P S.q c.h S.cursor) := by ring
    _ ≤ potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
          (terminalFailureBranchLoad c) +
        (c.Cdir * w.alphaX * detLoss P S.q S.cursor (S.cursor + c.h) +
         c.Cdir * w.alphaX * serviceWindowCharge P S.q c.h S.cursor) :=
      add_le_add hload (add_le_add hlossBound hserviceBound)
    _ = potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
          (terminalFailureBranchLoad c) + c.Cdir * w.alphaX *
        (detLoss P S.q S.cursor (S.cursor + c.h) +
          serviceWindowCharge P S.q c.h S.cursor) := by ring

/-- A calm T3 service update retains zero drift and pays the strict profile
work decrement. -/
theorem branchT3CalmRow (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H .t3 S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hprofileFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤)
    (hratio : adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + c.h) ≤ c.rDr)
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    PotentialRow w .t3
      (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch
          (advanceCursor P S (S.cursor + c.h) .search none) -
       statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S)
      (transitionCharge P c.h c.l0 H S .t3) := by
  rcases hsearch with ⟨hphase, hstart, -⟩
  rcases hguard with ⟨-, hdriftZero, habove⟩
  obtain ⟨hpos, hmono, hloss, hservice⟩ :=
    serviceIntervalData (c := c) hP hunit hexact hread hstart
  have hcalm := driftIndex_calm hd (initExpRhoDr_pos hg).le c.etaPre_pos S
    (hexact.2.2.2.2.1.trans hexact.2.2.2.2.2) c.one_le_h
    c.drift_service_le hratio c.rDr_pow_le c.rDr_drift hpos hmono
  have hwork := serviceWork_decrement_le (c := c) hd hP hunit hexact hread
    hstart hprofileFinite habove
  have hdriftNext := hcalm.2 hdriftZero
  have hdriftReal : (driftIndex P (initExpRhoDr g) c.etaPre jStar
        (advanceCursor P S (S.cursor + c.h) .search none) : ℝ) ≤
      (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) + 0 := by
    have hnext : driftIndex P (initExpRhoDr g) c.etaPre jStar
        (advanceCursor P S (S.cursor + c.h) .search none) = 0 := by
      simpa only [driftIndex, advanceCursor] using hdriftNext
    rw [hnext, hdriftZero]
    norm_num
  have hwork' : c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar
          (advanceCursor P S (S.cursor + c.h) .search none) ≤
      c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) c.etaReady jStar S +
        (-c.etaReady * potentialWorkDecrement c +
          c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) *
            serviceWindowCharge P S.q c.h S.cursor) := by
    linarith only [hwork]
  have hraw := servicePotentialChange_le (c := c) hphase hwork' hdriftReal w
  apply PotentialRow.t3Calm
  change _ ≤ -w.alphaW * potentialWorkDecrement c +
    c.Cdir * w.alphaX *
      (detLoss P S.q S.cursor (S.cursor + c.h) +
        serviceWindowCharge P S.q c.h S.cursor)
  have hterm := serviceTerm_le_weightedCharge (c := c) hloss hservice w
  rw [w.alphaW_eq] at hraw ⊢
  linarith only [hraw, hterm]

/-- A noncalm T2 update is paid by the common determinant charge scale. -/
theorem branchT2NoncalmRow (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H .t2 S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hprofileFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤)
    (hratio : c.rDr < adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + c.h))
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
  rcases hsearch with ⟨-, hstart, -⟩
  rcases hguard with ⟨hphase, -⟩
  obtain ⟨-, -, -, hservice⟩ :=
    serviceIntervalData (c := c) hP hunit hexact hread hstart
  have hscale : potentialScale c < transitionCharge P c.h c.l0 H S .t2 := by
    rw [transitionCharge_eq]
    exact lt_of_lt_of_le (serviceNoncalmScale (c := c) hexact hread hratio)
      (le_add_of_nonneg_right hservice)
  apply PotentialRow.t2Noncalm hscale
  change _ ≤ potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
      (terminalFailureBranchLoad c) + c.Cdir * w.alphaX *
    (detLoss P S.q S.cursor (S.cursor + c.h) +
      serviceWindowCharge P S.q c.h S.cursor)
  exact noncalmServicePotential_le (c := c) hd hg hP hunit hexact hphase
    hstart hread hprofileFinite w

/-- A noncalm T3 update obeys the same expensive determinant-charge row. -/
theorem branchT3NoncalmRow (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H .t3 S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hprofileFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤)
    (hratio : c.rDr < adaptedDetRoot P S.q S.cursor /
      adaptedDetRoot P S.q (S.cursor + c.h))
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    PotentialRow w .t3
      (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch
          (advanceCursor P S (S.cursor + c.h) .search none) -
       statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S)
      (transitionCharge P c.h c.l0 H S .t3) := by
  rcases hsearch with ⟨-, hstart, -⟩
  rcases hguard with ⟨hphase, -, -⟩
  obtain ⟨-, -, -, hservice⟩ :=
    serviceIntervalData (c := c) hP hunit hexact hread hstart
  have hscale : potentialScale c < transitionCharge P c.h c.l0 H S .t3 := by
    rw [transitionCharge_eq]
    exact lt_of_lt_of_le (serviceNoncalmScale (c := c) hexact hread hratio)
      (le_add_of_nonneg_right hservice)
  apply PotentialRow.t3Noncalm hscale
  change _ ≤ potentialLoad c (startupBranchLoad c) (shortFailureBranchLoad c)
      (terminalFailureBranchLoad c) + c.Cdir * w.alphaX *
    (detLoss P S.q S.cursor (S.cursor + c.h) +
      serviceWindowCharge P S.q c.h S.cursor)
  exact noncalmServicePotential_le (c := c) hd hg hP hunit hexact hphase
    hstart hread hprofileFinite w

end

end Homogenization.HighContrast.Selection
