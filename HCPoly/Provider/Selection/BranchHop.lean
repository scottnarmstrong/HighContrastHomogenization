/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchHopData

/-!
# The projective-hop branch

The analytic T5 data imply the scalar potential row and the common one-step
potential inequality for the successor chosen by the transition system.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

private theorem driftIndex_le_bHop {P : Measure (CoeffSpace d)}
    {rhoDr : ℝ} {jStar : ℤ} {S : State d}
    (hdrift : linearDrift P rhoDr S.q jStar S.cursor ≤ c.etaNew) :
    driftIndex P rhoDr c.etaPre jStar S ≤ c.bHop := by
  have hratio := div_le_div_of_nonneg_right hdrift c.etaPre_pos.le
  have hmax : max 1 (linearDrift P rhoDr S.q jStar S.cursor / c.etaPre) ≤
      max 1 (c.etaNew / c.etaPre) := max_le_max le_rfl hratio
  have hx : 0 < max 1 (linearDrift P rhoDr S.q jStar S.cursor / c.etaPre) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hmax
  simpa only [driftIndex, c.bHop_eq] using Nat.ceil_mono hlog

/-- The retained aligned providers prove the analytic data, scalar row, and
common one-step inequality for an actual T5 successor. -/
theorem branchT5_of_alignedConstant (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {source : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K source)
    {jStar M : ℤ} (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    (hbridge : ∀ mp mv : Mat d, mp.PosDef → mv.PosDef → ∀ nn l : ℤ,
      jStar ≤ nn - l →
      Ctr * (1 + Real.log (gridRatio (roundedGrid jStar mp)
        (roundedGrid jStar mv))) ≤ (l : ℝ) →
      Ctr * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
        (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
      (∀ r : Mat d, r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l → adaptedCell r j ⊆ centeredCube d M) →
      BlockMatLoewnerLE
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn - l)))
          (blockScale (bridgeErrUpper Ctr Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) nn)) ∧
        BlockMatLoewnerLE
          (blockScale (-bridgeErrLower Ctr Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn + l))) ∧
        ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
          BlockMatLoewnerLE (blockScale (1 - eta)
            (adaptedMean P (roundedGrid jStar mp) (nn + l)))
            (adaptedMean P (roundedGrid jStar mv) nn) →
          linearDrift P (initExpRhoDr g) (roundedGrid jStar mv) jStar nn ≤
            Ctr * (eta + gridRatio (roundedGrid jStar mp)
                (roundedGrid jStar mv) * (3 : ℝ) ^ (-(l : ℝ)) +
              (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
                (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                linearDrift P (initExpRhoDr g) (roundedGrid jStar mp)
                  jStar (nn + l) +
              bridgeShiftedRemainder Ctr Cd g (initExpRhoDr g) E
                jStar mp mv nn l))
    {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}
    (z : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {S S' : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hsearch : SearchInvariant c.h S) (hbase : S.base = S.checkpoint)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      c.deltaShort c.deltaTerm c.l0 H .t5 S)
    (hout : (selectorStep P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm S).outcome = StepOutcome.next S')
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + 2 * (c.l0 : ℤ)))
    {r0 : ℤ} {k : ℕ} (cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 k)
    (hmu : cert.mus k = S.mu) (hstage : cert.starts k ≤ S.cursor)
    (hentry : z.B * Real.logb 3 (2 + aspectRatio E) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hcont : ∀ r : Mat d, r = S.q ∨ r = S'.q → ∀ j : ℤ,
      jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
        adaptedCell r j ⊆ centeredCube d M)
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g)) :
    let step := selectorStep P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm S
    step.rule = .t5 ∧ S'.mu.PosDef ∧
      stateHistory S' ≤ ENNReal.ofReal c.etaIn ∧
      linearDrift P (initExpRhoDr g) S'.q jStar S'.cursor ≤ c.etaNew ∧
      projDist S.mu S'.mu ≤ c.chop ∧ gridRatio S.q S'.q ≤ Khop ∧
      BlockMatLoewnerLE (blockScale (1 - c.etaX)
        (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ))))
        (adaptedMean P S'.q (S.cursor + (c.l0 : ℤ))) ∧
      BlockMatLoewnerLE (adaptedMean P S'.q (S.cursor + (c.l0 : ℤ)))
        (blockScale (1 + c.etaX)
          (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ)))) ∧
      stateProfile P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) jStar S' = stateHistory S' ∧
      PotentialRow w .t5
        (statePotential P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
            w.alphaW w.alphaX w.alphaFresh w.alphaSearch S' -
          statePotential P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
            w.alphaW w.alphaX w.alphaFresh w.alphaSearch S)
        (transitionCharge P c.h c.l0 H S .t5) ∧
      statePotential P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
          w.alphaW w.alphaX w.alphaFresh w.alphaSearch S' ≤
        statePotential P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
            w.alphaW w.alphaX w.alphaFresh w.alphaSearch S - w.c0 - w.mHop +
          w.Cdet * transitionCharge P c.h c.l0 H S .t5 := by
  dsimp only
  obtain ⟨hrule, hmuPos, hnewPos, hhistory, hdrift, hjump, hratio, hlo, hhi,
      hprofile⟩ := branchT5Data_of_alignedConstant hd hg hCd hstat hunit hdag
        hwin hY hbridge z hexact hsearch hguard hout hread cert hmu hstage hentry hcont
  have hselected := ruleGuard_unique P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
    c.deltaShort c.deltaTerm c.l0 H S .t5 hguard
  have houtEq := hout
  simp [selectorStep, ← hselected] at houtEq
  subst S'
  let t0 : ℤ := S.cursor + 2 * (c.l0 : ℤ)
  let n : ℤ := S.cursor + (c.l0 : ℤ)
  let F : BlockMat d := adaptedMean P S.q t0
  let mu' : Mat d := projPathStep c.chop S.mu (canonicalMetric F)
  let q' : Mat d := roundedGrid jStar mu'
  have hmu'pos : mu'.PosDef := by
    simpa [hopState, t0, n, F, mu', q'] using hmuPos
  have hnewPos' : Matrix.PosDef (toFullBlockMat (adaptedMean P q' n)) := by
    simpa [hopState, t0, n, F, mu', q'] using hnewPos
  have hlo' : BlockMatLoewnerLE (blockScale (1 - c.etaX) F)
      (adaptedMean P q' n) := by
    simpa [hopState, t0, n, F, mu', q'] using hlo
  have hhi' : BlockMatLoewnerLE (adaptedMean P q' n)
      (blockScale (1 + c.etaX) F) := by
    simpa [hopState, t0, n, F, mu', q'] using hhi
  have hjcursor : jStar ≤ S.cursor :=
    hexact.2.2.2.2.1.trans hexact.2.2.2.2.2
  have hcursorT : S.cursor ≤ t0 := by dsimp [t0]; omega
  have hjbase : jStar ≤ S.base := by rw [hbase]; exact hexact.2.2.2.2.1
  have hbaseT : S.base ≤ t0 := by
    rw [hbase]
    exact hexact.2.2.2.2.2.trans hcursorT
  obtain ⟨hmean, -, -, -, -, -, -, -, -⟩ :=
    c.portableData.law P inferInstance hstat hunit jStar S.q hread.rounded
      jStar S.checkpoint t0 le_rfl hexact.2.2.2.2.1
      (hexact.2.2.2.2.2.trans hcursorT)
      hread.finiteMean hread.positiveMean hread.finiteMoment
  have hwork : c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) c.etaReady jStar
      (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        jStar c.chop c.l0 S) ≤
      c.etaReady * Real.log (1 + c.etaIn / c.etaReady) := by
    change c.etaReady * Real.log (1 + c.etaReady⁻¹ *
        (stateProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar
            (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
              jStar c.chop c.l0 S)).toReal) ≤
      c.etaReady * Real.log (1 + c.etaIn / c.etaReady)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hprofile.trans_le hhistory)
    rw [ENNReal.toReal_ofReal c.etaIn_pos.le] at hr
    have hfrac : c.etaReady⁻¹ *
        (stateProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar
            (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
              jStar c.chop c.l0 S)).toReal ≤ c.etaIn / c.etaReady := by
      rw [inv_mul_eq_div]
      exact (div_le_div_iff_of_pos_right c.etaReady_pos).2 hr
    have harg : 0 < 1 + c.etaReady⁻¹ *
        (stateProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar
            (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
              jStar c.chop c.l0 S)).toReal := by
      have hm : 0 ≤ c.etaReady⁻¹ *
          (stateProfile P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) jStar
              (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
                jStar c.chop c.l0 S)).toReal :=
        mul_nonneg (inv_nonneg.mpr c.etaReady_pos.le) ENNReal.toReal_nonneg
      linarith only [hm]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log harg (by linarith only [hfrac]))
      c.etaReady_pos.le
  have hb := driftIndex_le_bHop (c := c) hdrift
  have hwd : c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar
        (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          jStar c.chop c.l0 S) +
      (driftIndex P (initExpRhoDr g) c.etaPre jStar
        (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          jStar c.chop c.l0 S) : ℝ) ≤ hopBranchLoad c := by
    rw [hopBranchLoad_eq]
    exact add_le_add hwork (by exact_mod_cast hb)
  have hbasePos := hread.positiveMean S.base
    hjbase hbaseT
  have hFPos := hread.positiveMean t0 (hjcursor.trans hcursorT) le_rfl
  have hFA := le_of_blockMatLoewnerLE
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t0)
    (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.base)
    (hmean S.base t0 hjbase hbaseT le_rfl)
  have hlowFull := le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_blockScale (1 - c.etaX)
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t0))
    (Recurrence.isSymmetricBlockMat_adaptedMean P q' n) hlo'
  have hhiFull := le_of_blockMatLoewnerLE
    (Recurrence.isSymmetricBlockMat_adaptedMean P q' n)
    (isSymmetricBlockMat_blockScale (1 + c.etaX)
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t0)) hhi'
  rw [toFullBlockMat_blockScale] at hlowFull hhiFull
  have hcurLoss := detLoss_nonneg_of_meanOrder
    (hread.positiveMean S.cursor hjcursor hcursorT) hFPos
    (hmean S.cursor t0 hjcursor hcursorT le_rfl)
  have hbaseLoss := detLoss_nonneg_of_meanOrder hbasePos hFPos
    (hmean S.base t0 hjbase hbaseT le_rfl)
  have hcharge : 0 ≤ transitionCharge P c.h c.l0 H S .t5 := by
    simpa [transitionCharge, t0] using add_nonneg hcurLoss hbaseLoss
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hmus : S.mu.PosDef := by rw [← hmu]; exact cert.mus_pos k le_rfl
  have hbaseCanonPos := ShortHop.posDef_canonicalMetric
    (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.base)
      hbasePos)
  have holdWork : 0 ≤ c.etaReady * stateWork P (initExpQ d g : ℝ)
      (initExpA g) (initExpRhoMax d g) c.etaReady jStar S := by
    apply mul_nonneg c.etaReady_pos.le
    apply Real.log_nonneg
    have hm : 0 ≤ c.etaReady⁻¹ * (stateProfile P (initExpQ d g : ℝ)
        (initExpA g) (initExpRhoMax d g) jStar S).toReal :=
      mul_nonneg (inv_nonneg.mpr c.etaReady_pos.le) ENNReal.toReal_nonneg
    linarith only [hm]
  have holdDrift : 0 ≤ (driftIndex P (initExpRhoDr g) c.etaPre jStar S : ℝ) :=
    Nat.cast_nonneg _
  have holdProj := mul_nonneg w.alphaX_nonneg (projDist_nonneg hmus hbaseCanonPos)
  have hrow : PotentialRow w .t5
      (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch
          (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            jStar c.chop c.l0 S) -
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S)
      (transitionCharge P c.h c.l0 H S .t5) := by
    have htargetPos := ShortHop.posDef_canonicalMetric
      (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t0) hFPos)
    by_cases hfinal : projDist S.mu (canonicalMetric F) ≤ c.chop
    · apply PotentialRow.t5Final
      have hpath := projPathStep_eq_target hmus htargetPos hfinal
      have hproj := projective_progress_final hd
        (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t0) hFPos)
        hnewPos'
        c.etaX_pos.le c.etaX_le_quarter hlowFull hhiFull
      simp [statePotential, stateProjectiveDistance, hopState, hfinal, hguard.1,
        t0, n, F, mu', q', hpath, w.alphaW_eq, hexact.2.1] at hwd hproj ⊢
      have hp := mul_le_mul_of_nonneg_left hproj w.alphaX_nonneg
      linarith only [hwd, hp, holdWork, holdDrift, holdProj]
    · apply PotentialRow.t5Nonfinal
      have hres := projDist_projPathStep_target_le c.chop_pos hmus htargetPos
        (lt_of_not_ge hfinal)
      let ceff := projDist S.mu (canonicalMetric F) - projDist mu' (canonicalMetric F)
      have hceff : c.chop ≤ ceff := by dsimp [ceff]; linarith only [hres]
      have hdelta : detLoss P S.q S.base t0 =
          Real.log (detRoot d (adaptedMean P S.q S.base)) -
            Real.log (detRoot d F) := by simp [detLoss, adaptedDetRoot, F]
      have hproj0 := projective_progress_nonfinal (chop := ceff) hd
        (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.base) hbasePos)
        (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t0) hFPos)
        hnewPos' hFA hdelta c.etaX_pos.le c.etaX_le_quarter hlowFull hhiFull hmus
        hmu'pos (by dsimp only [ceff]; ring)
      have hproj : projDist mu' (canonicalMetric (adaptedMean P q' n)) ≤
          projDist S.mu (canonicalMetric (adaptedMean P S.q S.base)) - c.chop +
            ((d : ℝ) / 2) * detLoss P S.q S.base t0 +
              projectiveError c.etaX := by
        linarith only [hproj0, hceff]
      have hslope : (d : ℝ) / 2 * w.alphaX ≤ w.Cdet / 4 := by
        rw [w.Cdet_eq_mul]
        have hn := (normalizedConstant_bounds (c := c)).2.1
        nlinarith only [mul_le_mul_of_nonneg_right hn w.alphaX_nonneg]
      have hpay : w.alphaX * ((d : ℝ) / 2 * detLoss P S.q S.base t0) ≤
          w.Cdet / 4 * transitionCharge P c.h c.l0 H S .t5 := by
        have hm := mul_le_mul_of_nonneg_right hslope hbaseLoss
        simp only [transitionCharge]
        nlinarith only [hm, hcurLoss, w.Cdet_pos]
      simp [statePotential, stateProjectiveDistance, hopState, hfinal, hguard.1,
        t0, n, F, mu', q', w.alphaW_eq, w.alphaFresh_eq,
        hexact.2.1] at hwd hproj ⊢
      have hp := mul_le_mul_of_nonneg_left hproj w.alphaX_nonneg
      linarith only [hwd, hp, hpay, holdWork, holdDrift, holdProj,
        w.alphaSearch_pos.le, w.Gfresh_pos.le]
  have hone := PotentialRow.oneStepPotential w hcharge hrow
  have hone' :
      statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch
            (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
              jStar c.chop c.l0 S) -
          statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S ≤
        -w.c0 - w.mHop +
          w.Cdet * transitionCharge P c.h c.l0 H S .t5 := by
    simpa using hone
  refine ⟨hrule, hmuPos, hhistory, hdrift, hjump, hratio, hlo, hhi, hprofile, hrow, ?_⟩
  calc
    _ = statePotential P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
          w.alphaW w.alphaX w.alphaFresh w.alphaSearch S +
        (statePotential P (initExpQ d g : ℝ) (initExpA g)
              (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
              w.alphaW w.alphaX w.alphaFresh w.alphaSearch
              (hopState P (initExpQ d g : ℝ) (initExpA g)
                (initExpRhoMax d g) jStar c.chop c.l0 S) -
            statePotential P (initExpQ d g : ℝ) (initExpA g)
              (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
              w.alphaW w.alphaX w.alphaFresh w.alphaSearch S) := by ring
    _ ≤ statePotential P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
          w.alphaW w.alphaX w.alphaFresh w.alphaSearch S +
        (-w.c0 - w.mHop +
          w.Cdet * transitionCharge P c.h c.l0 H S .t5) :=
      add_le_add_right hone' _
    _ = _ := by ring

end

end Homogenization.HighContrast.Selection
