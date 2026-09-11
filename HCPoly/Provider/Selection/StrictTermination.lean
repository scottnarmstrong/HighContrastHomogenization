/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Branches
import HCPoly.Provider.Selection.StrictArithmetic
import HCPoly.Provider.Selection.StrictTelescope

/-!
# Strict termination of the actual selector run

The actual branch rows telescope, the synchronized-service account bounds the
total determinant charge, and the preselected hop debit cancels its hop part.
The resulting strict cap comparison forces the executable run to terminate.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The source-selected capped run uses strictly fewer than all available
transitions and therefore reaches its terminal rule. -/
theorem selectionRun_strictly_terminates (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd)
    (hetaProfBar : etaProfBar ≤ 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {source : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K source)
    {jStar Mexec : ℤ}
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Psi K Cd jStar Mexec Y)
    (hbridge : ∀ mp mv : Mat d, mp.PosDef → mv.PosDef → ∀ nn l : ℤ,
      jStar ≤ nn - l →
      Ctr * (1 + Real.log (gridRatio (roundedGrid jStar mp)
        (roundedGrid jStar mv))) ≤ (l : ℝ) →
      Ctr * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
        (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
      (∀ r : Mat d, r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
          adaptedCell r j ⊆ centeredCube d Mexec) →
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
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g))
    {Chit Bmin : ℝ}
    (cc : CutoffConstants c w.alphaFresh w.alphaX
      (2 * (d : ℝ) * Real.log 12) w.c0 Chit Bmin)
    {Lam : ℝ} (hLamEq : Lam = Real.logb 3 (2 + aspectRatio E))
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    {r0 : ℤ} {A0 : BlockMat d} {hcen hnl : ℝ≥0∞}
    (hstart : jStar + ⌈cc.B * Lam⌉ ≤ r0)
    (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hexact0 : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar (initialState r0 A0 hcen hnl))
    (hfresh0 : FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar
      (initialState r0 A0 hcen hnl))
    (hroot0 : adaptedDetRoot P (1 : Mat d) r0 ≤ 24 * aspectRatio E)
    (hpotential0 : statePotential P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      w.alphaW w.alphaX w.alphaFresh w.alphaSearch
        (initialState r0 A0 hcen hnl) ≤ cc.CF * Lam) :
    let run := selectionRun cc P jStar Lam r0 A0 hcen hnl
    ((run.transitionCount : ℝ) ≤ cc.CN * Lam) ∧
      run.transitionCount < transitionCap cc.CN Lam ∧
      run.outcome = .terminal (runFinalState run) := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hPi : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hLam : 1 ≤ Lam := by
    rw [hLamEq]
    exact ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hceil0 : (0 : ℤ) ≤ ⌈cc.B * Lam⌉ :=
    Int.ceil_nonneg (mul_nonneg cc.B_pos.le (le_trans zero_le_one hLam))
  have hj0 : jStar ≤ r0 := by omega
  have hentryLam : cc.B * Lam ≤ (r0 : ℝ) - (jStar : ℝ) := by
    have hceilLe : cc.B * Lam ≤ (⌈cc.B * Lam⌉ : ℤ) := Int.le_ceil _
    have hstartReal : ((jStar + ⌈cc.B * Lam⌉ : ℤ) : ℝ) ≤ (r0 : ℝ) := by
      exact_mod_cast hstart
    push_cast at hstartReal
    linarith only [hceilLe, hstartReal]
  have hentry : cc.B * Real.logb 3 (2 + aspectRatio E) ≤
      (r0 : ℝ) - (jStar : ℝ) := by
    rw [← hLamEq]
    exact hentryLam
  let run := selectionRun cc P jStar Lam r0 A0 hcen hnl
  let F : State d → ℝ := fun S ↦
    statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
      (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
      w.alphaFresh w.alphaSearch S
  change ((run.transitionCount : ℝ) ≤ cc.CN * Lam) ∧
    run.transitionCount < transitionCap cc.CN Lam ∧
    run.outcome = .terminal (runFinalState run)
  have hstep : ∀ i : ℕ, ∀ S₀ S₁ : State d,
      run.states[i]? = some S₀ → run.states[i + 1]? = some S₁ →
        ∃ rule : TransitionRule, run.rules[i]? = some rule ∧
          F S₁ ≤ F S₀ - w.c0 - w.mHop *
            (if rule = TransitionRule.t5 then 1 else 0) +
              w.Cdet * transitionCharge P c.h c.l0 H S₀ rule := by
    intro i S₀ S₁ h₀ h₁
    obtain ⟨rule, hrule, -, hone⟩ := selectionRun_consecutive_row hd hg hCd
      hetaProfBar hstat hunit hdag hwin hY hbridge cc hLam hj0 hr0 hMexec
      hexact0 hfresh0 hentry w (by simpa only [run] using h₀)
      (by simpa only [run] using h₁)
    exact ⟨rule, by simpa only [run] using hrule, by simpa only [F] using hone⟩
  have hrawStep :
      let raw := runCapped P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
        c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
        (initialState r0 A0 hcen hnl)
      ∀ i : ℕ, ∀ S₀ S₁ : State d,
        raw.states[i]? = some S₀ → raw.states[i + 1]? = some S₁ →
          ∃ rule : TransitionRule, raw.rules[i]? = some rule ∧
            F S₁ ≤ F S₀ - w.c0 - w.mHop *
              (if rule = TransitionRule.t5 then 1 else 0) +
                w.Cdet * transitionCharge P c.h c.l0 H S₀ rule := by
    simpa only [run, selectionRun] using hstep
  have htelRaw := runCapped_potential_bound_of_consecutive P
    (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) (initExpRhoDr g)
    jStar c.h c.chop c.l0 H c.etaReady c.etaPre c.deltaShort c.deltaTerm
    (transitionCap cc.CN Lam) (initialState r0 A0 hcen hnl) F hrawStep
  have htel : w.c0 * (run.transitionCount : ℝ) +
      w.mHop * (run.rules.count TransitionRule.t5 : ℝ) ≤
        F (initialState r0 A0 hcen hnl) - F (runFinalState run) +
          w.Cdet * runTransitionSum (transitionCharge P c.h c.l0 H) run := by
    simpa only [run, selectionRun] using htelRaw
  have hfinalMem : runFinalState run ∈ run.states := by
    simpa only [run, selectionRun] using runCapped_finalState_mem P
      (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) (initExpRhoDr g)
      jStar c.h c.chop c.l0 H c.etaReady c.etaPre c.deltaShort c.deltaTerm
      (transitionCap cc.CN Lam) (initialState r0 A0 hcen hnl)
  have hgeom := selectionRun_state_geometry hd cc hLam hwin hj0 hr0 hMexec
    A0 hcen hnl hY
  have hdefined := selectionRun_states_definedness_and_mean_order hd hg cc hstat
    hdag.refBlock_isSymm hLam hwin hj0 hr0 hMexec A0 hcen hnl hY
  obtain ⟨hexactFinal, -, hcursorFinal, -⟩ := selectionRun_state_invariants
    hd hg hCd hstat hunit hdag hwin hY hbridge cc hLam hj0 hr0 hMexec
      hexact0 hfresh0 hentry (runFinalState run) hfinalMem
  obtain ⟨-, hjbaseFinal, hbaseCursorFinal, hmuFinal, -, -, -, -⟩ :=
    hgeom (runFinalState run) hfinalMem
  have hbasePos : Book.Ch02.BlockPosDef (runFinalState run).baseMean := by
    rw [hexactFinal.2.1]
    exact (hdefined.1 (runFinalState run) hfinalMem (runFinalState run).base
      hjbaseFinal (hbaseCursorFinal.trans hcursorFinal)).2.1
  have hbaseFull : (toFullBlockMat (runFinalState run).baseMean).PosDef :=
    posDef_toFullBlockMat (by rw [hexactFinal.2.1]; exact
      Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hbasePos
  have hfinalNonneg : 0 ≤ F (runFinalState run) := by
    simpa only [F] using statePotential_nonneg_of_posDef w hmuFinal hbaseFull
  have hpotential : w.c0 * (run.transitionCount : ℝ) +
      w.mHop * (run.rules.count TransitionRule.t5 : ℝ) ≤
        cc.CF * Lam +
          w.Cdet * runTransitionSum (transitionCharge P c.h c.l0 H) run := by
    have hinitial : F (initialState r0 A0 hcen hnl) ≤ cc.CF * Lam := by
      simpa only [F] using hpotential0
    linarith only [htel, hinitial, hfinalNonneg]
  have hpos : ∀ S' ∈ run.states, ∀ u : ℤ, S'.base ≤ u →
      u ≤ run.queryScale → Book.Ch02.BlockPosDef (adaptedMean P S'.q u) := by
    intro S' hS' u hbaseu hu
    have hjbase := (hgeom S' hS').2.1
    exact (hdefined.1 S' hS' u (hjbase.trans hbaseu) hu).2.1
  have hmean : ∀ S' ∈ run.states, ∀ u v : ℤ, S'.base ≤ u → u ≤ v →
      v ≤ run.queryScale →
        BlockMatLoewnerLE (adaptedMean P S'.q v) (adaptedMean P S'.q u) := by
    intro S' hS' u v hbaseu huv hv
    have hjbase := (hgeom S' hS').2.1
    exact hdefined.2 S' hS' u v (hjbase.trans hbaseu) huv hv
  have hchargeRaw := runCapped_initial_transitionCharge_le_mul_prefixLoss P
    (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) (initExpRhoDr g)
    jStar c.h r0 c.chop c.l0 H (transitionCap cc.CN Lam) c.etaReady c.etaPre
    c.deltaShort c.deltaTerm A0 hcen hnl c.one_le_h
  dsimp only at hchargeRaw
  have hcharge : runTransitionSum (transitionCharge P c.h c.l0 H) run ≤
      ((c.h : ℝ) + 2) * (runFinalState run).prefixLoss := by
    apply hchargeRaw
    · simpa only [run, selectionRun] using hpos
    · simpa only [run, selectionRun] using hmean
  have hprefix := selectionRun_state_prefixLoss_le hd hg hCd hstat hunit hdag
    hwin hY hbridge cc hLam hj0 hr0 hMexec hexact0 hfresh0 hentry hroot0 hfinalMem
  have hlastRaw := runCapped_finalState_getLast? P (initExpQ d g : ℝ)
    (initExpA g) (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
    c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl)
  have hstageRaw := runCapped_last_stage_eq P (initExpQ d g : ℝ)
    (initExpA g) (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
    c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl) (runFinalState run) hlastRaw
  have hstage : (runFinalState run).stage =
      run.rules.count TransitionRule.t5 := by
    simpa only [run, selectionRun, initialState, zero_add] using hstageRaw
  rw [hstage] at hprefix
  have hhTwo : 0 ≤ (c.h : ℝ) + 2 := by
    have hh : (1 : ℝ) ≤ c.h := by exact_mod_cast c.one_le_h
    linarith only [hh]
  have hchargeBound : runTransitionSum (transitionCharge P c.h c.l0 H) run ≤
      ((c.h : ℝ) + 2) * (Real.log (24 * aspectRatio E) +
        2 * (run.rules.count TransitionRule.t5 : ℝ) * Real.log (1 + c.etaX)) :=
    hcharge.trans (mul_le_mul_of_nonneg_left hprefix hhTwo)
  have hentryLog : Real.log (24 * aspectRatio E) ≤ Real.log 72 * Lam :=
    log_twentyFour_mul_le_log_seventyTwo_mul_logb hPi hLamEq
  have hCN : cc.CN =
      (cc.CF + w.Cdet * ((c.h : ℝ) + 2) * Real.log 72) / w.c0 := by
    rw [cc.CN_eq, transitionCoefficient_eq, ← w.Cdet_eq]
  have hcount : (run.transitionCount : ℝ) ≤ cc.CN * Lam :=
    transitionCount_le_of_hop_cancellation w.c0_pos w.Cdet_pos.le hhTwo
      w.mHop_eq hentryLog hchargeBound hpotential hCN
  have hstrict : run.transitionCount < transitionCap cc.CN Lam :=
    lt_transitionCap_of_real_le hcount
  have hterminalRaw := runCapped_terminal_of_transitionCount_lt_fuel P
    (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) (initExpRhoDr g)
    jStar c.h c.chop c.l0 H c.etaReady c.etaPre c.deltaShort c.deltaTerm
    (transitionCap cc.CN Lam) (initialState r0 A0 hcen hnl)
    (by simpa only [run, selectionRun] using hstrict)
  obtain ⟨T, hout⟩ := hterminalRaw
  have houtRun : run.outcome = .terminal T := by
    simpa only [run, selectionRun] using hout
  refine ⟨hcount, hstrict, ?_⟩
  rw [runFinalState_eq, houtRun]

end

end Homogenization.HighContrast.Selection
