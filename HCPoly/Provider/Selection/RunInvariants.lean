/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Enclosure
import HCPoly.Provider.Selection.BranchTrace
import HCPoly.Provider.Selection.RunInvariantStep

/-!
# Invariants of the actual selector run

Every state retained by the executable capped selector carries its exact
annealed data and phase invariant.  A proof-only hop certificate follows the
same trace without becoming a field of the selector state.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
variable {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}

/-- Every state of the actual capped run retains the exact state, phase, and
completed projective-hop prefix data. -/
theorem selectionRun_state_invariants (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd)
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
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {Lam : ℝ} (hLam : 1 ≤ Lam) {r0 : ℤ} (hj0 : jStar ≤ r0)
    (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    {A0 : BlockMat d} {hcen hnl : ℝ≥0∞}
    (hexact0 : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar (initialState r0 A0 hcen hnl))
    (hfresh0 : FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar
      (initialState r0 A0 hcen hnl))
    (hentry : cc.B * Real.logb 3 (2 + aspectRatio E) ≤
      (r0 : ℝ) - (jStar : ℝ)) :
    ∀ T ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states,
      ExactStateData P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar T ∧
        T.base = T.checkpoint ∧
        T.cursor ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale ∧
        stateHistory T ≤ ENNReal.ofReal c.etaIn ∧
        (FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar T ∨
          SearchInvariant c.h T ∨
          TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew c.etaX jStar T ∧
            ∀ E0 : BlockMat d, T.candidate = some E0 →
              IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0) ∧
        ∃ cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 T.stage,
          cert.mus T.stage = T.mu ∧ cert.grids T.stage = T.q ∧
            cert.starts T.stage = T.base ∧
            T.prefixLoss = cert.completedLoss + detLoss P T.q T.base T.cursor ∧
            (∀ i : ℕ, i < T.stage →
              BlockMatLoewnerLE (blockScale (1 - cert.eta i)
                (adaptedMean P (cert.grids i) (cert.terminals i)))
                (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1))) ∧
              BlockMatLoewnerLE
                (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1)))
                (blockScale (1 + cert.eta i)
                  (adaptedMean P (cert.grids i) (cert.terminals i)))) ∧
            (∀ i : ℕ, i ≤ T.stage → cert.starts i ≤
              (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale) ∧
            (∀ i : ℕ, i < T.stage → cert.terminals i ≤
              (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale) ∧
            (∀ i : ℕ, i ≤ T.stage →
              HasFiniteAdaptedMean P (cert.grids i) (cert.starts i)) ∧
            (∀ i : ℕ, i < T.stage →
              HasFiniteAdaptedMean P (cert.grids i) (cert.terminals i)) ∧
            (∀ i : ℕ, i < T.stage → cert.eta i ≤ c.etaX) ∧
            cert.starts 0 = r0 := by
  let run := selectionRun cc P jStar Lam r0 A0 hcen hnl
  let Inv : State d → Prop := fun T ↦
    ExactStateData P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) jStar T ∧
      T.base = T.checkpoint ∧
      T.cursor ≤ run.queryScale ∧
      stateHistory T ≤ ENNReal.ofReal c.etaIn ∧
      (FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar T ∨
        SearchInvariant c.h T ∨
        TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew c.etaX jStar T ∧
          ∀ E0 : BlockMat d, T.candidate = some E0 →
            IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0) ∧
      ∃ cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 T.stage,
        cert.mus T.stage = T.mu ∧ cert.grids T.stage = T.q ∧
          cert.starts T.stage = T.base ∧
          T.prefixLoss = cert.completedLoss + detLoss P T.q T.base T.cursor ∧
          (∀ i : ℕ, i < T.stage →
            BlockMatLoewnerLE (blockScale (1 - cert.eta i)
              (adaptedMean P (cert.grids i) (cert.terminals i)))
              (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1))) ∧
            BlockMatLoewnerLE
              (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1)))
          (blockScale (1 + cert.eta i)
                (adaptedMean P (cert.grids i) (cert.terminals i)))) ∧
          (∀ i : ℕ, i ≤ T.stage → cert.starts i ≤ run.queryScale) ∧
          (∀ i : ℕ, i < T.stage → cert.terminals i ≤ run.queryScale) ∧
          (∀ i : ℕ, i ≤ T.stage →
            HasFiniteAdaptedMean P (cert.grids i) (cert.starts i)) ∧
          (∀ i : ℕ, i < T.stage →
            HasFiniteAdaptedMean P (cert.grids i) (cert.terminals i)) ∧
          (∀ i : ℕ, i < T.stage → cert.eta i ≤ c.etaX) ∧
          cert.starts 0 = r0
  have hgeom := selectionRun_state_geometry hd cc hLam hwin hj0 hr0 hMexec
    A0 hcen hnl hY
  have hdefined := selectionRun_states_definedness_and_mean_order hd hg cc hstat
    hdag.refBlock_isSymm hLam hwin hj0 hr0 hMexec A0 hcen hnl hY
  have hinitial : Inv (initialState r0 A0 hcen hnl) := by
    let cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 0 := {
      mus := fun _ ↦ 1
      grids := fun _ ↦ 1
      starts := fun _ ↦ r0
      terminals := fun _ ↦ r0
      eta := fun _ ↦ 0
      mus_pos := by intro _ _; exact Matrix.PosDef.one
      mus_zero := rfl
      grids_eq := by
        intro _ _
        simpa only [initialState] using hexact0.1
      starts_zero := le_rfl
      scale_step := by omega
      hop_step := by omega
      grid_step := by omega
      eta_nonneg := by omega
      eta_le := by omega
      terminal_ge := by omega
      completedLoss := 0
      completedLoss_eq := by simp }
    have hquery0 : r0 ≤ run.queryScale := by
      have hread0 := runCapped_initial_readScale_le_queryScale P
        (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) (initExpRhoDr g)
        jStar c.h c.chop c.l0 H (transitionCap cc.CN Lam) c.etaReady c.etaPre
        c.deltaShort c.deltaTerm (initialState r0 A0 hcen hnl)
      have hread0' : r0 + c.h ≤
          (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale := by
        simpa only [selectionRun, selectorStep, selectedRule, initialState] using hread0
      change r0 ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale
      have hh : 1 ≤ c.h := c.one_le_h
      omega
    have hinitMem : initialState r0 A0 hcen hnl ∈
        (selectionRun cc P jStar Lam r0 A0 hcen hnl).states := by
      simpa only [selectionRun] using runCapped_initial_mem P
        (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) (initExpRhoDr g)
        jStar c.h c.chop c.l0 H c.etaReady c.etaPre c.deltaShort c.deltaTerm
        (transitionCap cc.CN Lam) (initialState r0 A0 hcen hnl)
    refine ⟨hexact0, by simp [initialState], hquery0, hfresh0.2.2.2.2.1,
      Or.inl hfresh0, cert, ?_⟩
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp only [initialState, cert, detLoss_self, add_zero]
    · intro i hi
      simp only [initialState] at hi
      omega
    · intro _ _
      simpa only [cert] using hquery0
    · intro i hi
      simp only [initialState] at hi
      omega
    · intro _ _
      have hfin := (hdefined.1 (initialState r0 A0 hcen hnl) hinitMem r0 hj0
        (by simpa only [run] using hquery0)).1
      simpa only [cert] using! hfin
    · intro i hi
      simp only [initialState] at hi
      omega
    · intro i hi
      simp only [initialState] at hi
      omega
  have hnext : ∀ {S S' : State d}, S ∈ run.states → S' ∈ run.states →
      (selectorStep P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
        c.etaReady c.etaPre c.deltaShort c.deltaTerm S).outcome = .next S' →
      (selectorStep P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
        c.etaReady c.etaPre c.deltaShort c.deltaTerm S).readScale ≤ run.queryScale →
      Inv S → Inv S' := by
    intro S S' hS hS' hout hreadBound hInv
    have hSrun : S ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states := by
      simpa only [run] using hS
    have hS'run : S' ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states := by
      simpa only [run] using hS'
    obtain ⟨-, hjbase, hbaseCursor, -, hgrid, -, -, hcells⟩ := hgeom S hSrun
    obtain ⟨-, -, -, -, hgrid', -, -, hcells'⟩ := hgeom S' hS'run
    rcases hInv with ⟨hexact, hbaseCheckpoint, -, hhistory, hphase, cert, hmu, hq,
      hs, hloss, hcertBridge, hstartsBound, hterminalsBound, hfinStarts,
      hfinTerminals, hcertEta, hstartsZero⟩
    have hh0 : (0 : ℤ) ≤ c.h := le_trans (by omega) c.one_le_h
    have hbaseQuery' : S'.base ≤ run.queryScale :=
      (selectorStep_next_base_le_readScale hh0 hbaseCursor hout).trans hreadBound
    have hnewFinite : HasFiniteAdaptedMean P S'.q S'.base :=
      (hdefined.1 S' hS'run S'.base (hgeom S' hS'run).2.1 hbaseQuery').1
    refine selectorStep_next_invariants hd hg hCd hstat hunit hdag hwin hY hbridge
      cc hentry hjbase hbaseCursor hbaseCheckpoint hout hreadBound hnewFinite ?_ ?_
      hexact hhistory hphase cert hstartsZero hmu hq hs hloss hcertBridge hstartsBound
      hterminalsBound hfinStarts hfinTerminals hcertEta
    · intro hrule
      have ht : S.cursor + 2 * (c.l0 : ℤ) ≤ run.queryScale := by
        simpa only [selectorStep, hrule] using hreadBound
      have hdata := hdefined.1 S hSrun
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hgrid]
        exact Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hwin
          (hgeom S hSrun).2.2.2.1
      · intro j hj hjt
        exact (hdata j hj (hjt.trans ht)).1
      · intro j hj hjt
        exact (hdata j hj (hjt.trans ht)).2.1
      · intro j hj hjt
        exact (hdata j hj (hjt.trans ht)).2.2
    · intro hrule r hr j hj hjt
      have ht : S.cursor + 2 * (c.l0 : ℤ) ≤ run.queryScale := by
        simpa only [selectorStep, hrule] using hreadBound
      rcases hr with rfl | rfl
      · exact hcells j hj (hjt.trans ht)
      · exact hcells' j hj (hjt.trans ht)
  have hall := runCapped_invariant_aux
    (P := P) (Q := (initExpQ d g : ℝ)) (a := initExpA g)
    (rhoMax := initExpRhoMax d g) (rhoDr := initExpRhoDr g)
    (jStar := jStar) (h := c.h) (chop := c.chop) (l0 := c.l0) (H := H)
    (etaReady := c.etaReady) (etaPre := c.etaPre)
    (deltaShort := c.deltaShort) (deltaTerm := c.deltaTerm)
    (fuel := transitionCap cc.CN Lam) (S := initialState r0 A0 hcen hnl)
    (Inv := Inv) (full := run) (by simp [run, selectionRun])
    (by simp [run, selectionRun]) hnext hinitial
  intro T hT
  exact hall T (by simpa only [run, selectionRun] using hT)

end

end Homogenization.HighContrast.Selection
