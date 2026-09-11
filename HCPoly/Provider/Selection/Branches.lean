/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchHop
import HCPoly.Provider.Selection.BranchServiceCases
import HCPoly.Provider.Selection.BranchTerminal
import HCPoly.Provider.Selection.BranchTrace
import HCPoly.Provider.Selection.RunInvariants

/-!
# Branch rows along the actual selector run

Consecutive entries of the executable trace satisfy the corresponding scalar
potential row.  The proof dispatches the ordered rule actually stored in the
trace and obtains every analytic input from the retained run invariants.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
variable {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}

/-- Every recorded nonterminal adjacency satisfies its scalar branch row and
the common one-step potential inequality. -/
theorem selectionRun_consecutive_row (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd) (hetaProfBar : etaProfBar ≤ 1)
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
      (r0 : ℝ) - (jStar : ℝ))
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g))
    {i : ℕ} {S S' : State d}
    (h₀ : (selectionRun cc P jStar Lam r0 A0 hcen hnl).states[i]? = some S)
    (h₁ : (selectionRun cc P jStar Lam r0 A0 hcen hnl).states[i + 1]? = some S') :
    ∃ rule : TransitionRule,
      (selectionRun cc P jStar Lam r0 A0 hcen hnl).rules[i]? = some rule ∧
      PotentialRow w rule
        (statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S' -
          statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S)
        (transitionCharge P c.h c.l0 H S rule) ∧
      statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
          w.alphaFresh w.alphaSearch S' ≤
        statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (initExpRhoDr g) jStar c.etaReady c.etaPre w.alphaW w.alphaX
            w.alphaFresh w.alphaSearch S - w.c0 -
          w.mHop * (if rule = .t5 then 1 else 0) +
          w.Cdet * transitionCharge P c.h c.l0 H S rule := by
  let run := selectionRun cc P jStar Lam r0 A0 hcen hnl
  have h₀' := show (runCapped P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
      (initialState r0 A0 hcen hnl)).states[i]? = some S by
    simpa only [selectionRun] using h₀
  have h₁' := show (runCapped P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
      (initialState r0 A0 hcen hnl)).states[i + 1]? = some S' by
    simpa only [selectionRun] using h₁
  obtain ⟨rule, hrules, hlabel, hout⟩ := runCapped_consecutive P
    (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) (initExpRhoDr g)
    jStar c.h c.chop c.l0 H c.etaReady c.etaPre c.deltaShort c.deltaTerm
    (transitionCap cc.CN Lam) (initialState r0 A0 hcen hnl) h₀' h₁'
  have hSmem : S ∈ run.states := by exact List.mem_of_getElem? h₀
  have hS'mem : S' ∈ run.states := by exact List.mem_of_getElem? h₁
  obtain ⟨hexact, hbaseCheckpoint, -, hhistory, hphase, cert, hmu, hq, hs, hloss,
      hcertBridge, -, -, -, -, -, -⟩ := selectionRun_state_invariants hd hg hCd hstat hunit hdag hwin
    hY hbridge cc hLam hj0 hr0 hMexec hexact0 hfresh0 hentry S
      (by simpa only [run] using hSmem)
  obtain ⟨-, hjbase, hbaseCursor, hmuPos, hgrid, -, -, hcells⟩ :=
    selectionRun_state_geometry hd cc hLam hwin hj0 hr0 hMexec A0 hcen hnl hY S
      (by simpa only [run] using hSmem)
  obtain ⟨-, -, -, -, -, -, -, hcells'⟩ := selectionRun_state_geometry hd cc
    hLam hwin hj0 hr0 hMexec A0 hcen hnl hY S'
      (by simpa only [run] using hS'mem)
  have hdefined := selectionRun_states_definedness_and_mean_order hd hg cc hstat
    hdag.refBlock_isSymm hLam hwin hj0 hr0 hMexec A0 hcen hnl hY
  have hreadBound := runCapped_consecutive_readScale_le P (initExpQ d g : ℝ)
    (initExpA g) (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
    c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl) h₀' h₁'
  have hreadBoundRun :
      (selectorStep P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.h c.chop c.l0 H c.etaReady c.etaPre
        c.deltaShort c.deltaTerm S).readScale ≤ run.queryScale := by
    simpa only [run, selectionRun] using hreadBound
  have hreadAt (TMax : ℤ) (hTMax : TMax ≤ run.queryScale) :
      FixedGridReadData (g := g) P jStar S TMax := by
    have hdata := hdefined.1 S (by simpa only [run] using hSmem)
    refine ⟨?_, fun j hj hjt ↦ (hdata j hj (hjt.trans hTMax)).1,
      fun j hj hjt ↦ (hdata j hj (hjt.trans hTMax)).2.1,
      fun j hj hjt ↦ (hdata j hj (hjt.trans hTMax)).2.2⟩
    rw [hgrid]
    exact Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hwin hmuPos
  have hdet (u v : ℤ) (hju : jStar ≤ u) (huv : u ≤ v)
      (hv : v ≤ run.queryScale) : 0 ≤ detLoss P S.q u v :=
    detLoss_nonneg_of_meanOrder
      ((hdefined.1 S (by simpa only [run] using hSmem) u hju (huv.trans hv)).2.1)
      ((hdefined.1 S (by simpa only [run] using hSmem) v (hju.trans huv) hv).2.1)
      (hdefined.2 S (by simpa only [run] using hSmem) u v hju huv hv)
  have hselected : selectedRule P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      c.deltaShort c.deltaTerm c.l0 H S = rule := by
    cases hrule : selectedRule P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H S <;>
      simpa [selectorStep, hrule] using hlabel
  have hguard := selectedRule_guard P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
    c.deltaShort c.deltaTerm c.l0 H S
  rw [hselected] at hguard
  have hrules' : run.rules[i]? = some rule := by
    simpa only [run, selectionRun] using hrules
  have hfresh (hp : S.phase = .fresh) :
      FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar S := by
    rcases hphase with h | h | h
    · exact h
    · cases h.1.symm.trans hp
    · cases h.1.1.symm.trans hp
  have hsearch (hp : S.phase = .search) : SearchInvariant c.h S := by
    rcases hphase with h | h | h
    · cases h.1.symm.trans hp
    · exact h
    · cases h.1.1.symm.trans hp
  have hterminal (hp : S.phase = .terminal) :
      TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew c.etaX jStar S := by
    rcases hphase with h | h | h
    · cases h.1.symm.trans hp
    · cases h.1.symm.trans hp
    · exact h.1
  have hh0 : (0 : ℤ) ≤ c.h := le_trans (by omega) c.one_le_h
  have hl00 : (0 : ℤ) ≤ c.l0 := by omega
  have hmax0 : (0 : ℤ) ≤ max (H : ℤ) c.h :=
    hh0.trans (le_max_right (H : ℤ) c.h)
  cases rule with
  | t1 =>
      have ht : S.cursor + c.h ≤ run.queryScale := by
        simpa only [selectorStep, hselected] using hreadBoundRun
      have hread := hreadAt _ ht
      simp [selectorStep, hselected] at hout
      subst S'
      have hrow := branchT1Row (c := c) hd hg hetaProfBar hstat hunit hexact
        (hfresh hguard) hread w
      have hone := PotentialRow.oneStepPotential w
        (hdet _ _ (hexact.2.2.2.2.1.trans hexact.2.2.2.2.2) (by omega) ht) hrow
      refine ⟨.t1, hrules', hrow, ?_⟩
      simp only [if_neg (by decide : TransitionRule.t1 ≠ .t5), transitionCharge] at hone ⊢
      linarith only [hone]
  | t2 =>
      have ht : S.cursor + c.h ≤ run.queryScale := by
        simpa only [selectorStep, hselected] using hreadBoundRun
      have hread := hreadAt _ ht
      have hsearch' := hsearch hguard.1
      have hfinite := stateProfile_ne_top_of_history (c := c) hetaProfBar hstat hunit
        hexact hhistory hread (by omega)
      simp [selectorStep, hselected] at hout
      subst S'
      obtain ⟨-, -, hordinary, hservice⟩ :=
        serviceIntervalData (c := c) hstat hunit hexact hread hsearch'.2.1
      by_cases hratio : adaptedDetRoot P S.q S.cursor /
          adaptedDetRoot P S.q (S.cursor + c.h) ≤ c.rDr
      · have hrow := branchT2CalmRow (c := c) hd hg hstat hunit hexact hsearch'
          hguard hread hfinite hratio w
        have hone := PotentialRow.oneStepPotential w (add_nonneg hordinary hservice) hrow
        refine ⟨.t2, hrules', hrow, ?_⟩
        simp only [if_neg (by decide : TransitionRule.t2 ≠ .t5), transitionCharge] at hone ⊢
        linarith only [hone]
      · have hrow := branchT2NoncalmRow (c := c) hd hg hstat hunit hexact hsearch'
          hguard hread hfinite (lt_of_not_ge hratio) w
        have hone := PotentialRow.oneStepPotential w (add_nonneg hordinary hservice) hrow
        refine ⟨.t2, hrules', hrow, ?_⟩
        simp only [if_neg (by decide : TransitionRule.t2 ≠ .t5), transitionCharge] at hone ⊢
        linarith only [hone]
  | t3 =>
      have ht : S.cursor + c.h ≤ run.queryScale := by
        simpa only [selectorStep, hselected] using hreadBoundRun
      have hread := hreadAt _ ht
      have hsearch' := hsearch hguard.1
      have hfinite := stateProfile_ne_top_of_history (c := c) hetaProfBar hstat hunit
        hexact hhistory hread (by omega)
      simp [selectorStep, hselected] at hout
      subst S'
      obtain ⟨-, -, hordinary, hservice⟩ :=
        serviceIntervalData (c := c) hstat hunit hexact hread hsearch'.2.1
      by_cases hratio : adaptedDetRoot P S.q S.cursor /
          adaptedDetRoot P S.q (S.cursor + c.h) ≤ c.rDr
      · have hrow := branchT3CalmRow (c := c) hd hg hstat hunit hexact hsearch'
          hguard hread hfinite hratio w
        have hone := PotentialRow.oneStepPotential w (add_nonneg hordinary hservice) hrow
        refine ⟨.t3, hrules', hrow, ?_⟩
        simp only [if_neg (by decide : TransitionRule.t3 ≠ .t5), transitionCharge] at hone ⊢
        linarith only [hone]
      · have hrow := branchT3NoncalmRow (c := c) hd hg hstat hunit hexact hsearch'
          hguard hread hfinite (lt_of_not_ge hratio) w
        have hone := PotentialRow.oneStepPotential w (add_nonneg hordinary hservice) hrow
        refine ⟨.t3, hrules', hrow, ?_⟩
        simp only [if_neg (by decide : TransitionRule.t3 ≠ .t5), transitionCharge] at hone ⊢
        linarith only [hone]
  | t4 =>
      have ht : S.cursor + 2 * (c.l0 : ℤ) ≤ run.queryScale := by
        simpa only [selectorStep, hselected] using hreadBoundRun
      have hread := hreadAt _ ht
      simp [selectorStep, hselected] at hout
      subst S'
      have hrow := branchT4Row (c := c) hd hg hstat hunit hexact
        (hsearch hguard.1) hguard hread w
      have hone := PotentialRow.oneStepPotential w
        (hdet _ _ (hexact.2.2.2.2.1.trans hexact.2.2.2.2.2) (by omega) ht) hrow
      refine ⟨.t4, hrules', hrow, ?_⟩
      simp only [if_neg (by decide : TransitionRule.t4 ≠ .t5), transitionCharge] at hone ⊢
      linarith only [hone]
  | t5 =>
      have ht : S.cursor + 2 * (c.l0 : ℤ) ≤ run.queryScale := by
        simpa only [selectorStep, hselected] using hreadBoundRun
      have hread := hreadAt _ ht
      have hcont : ∀ r : Mat d, r = S.q ∨ r = S'.q → ∀ j : ℤ,
          jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
            adaptedCell r j ⊆ centeredCube d Mexec := by
        intro r hr j hj hjt
        rcases hr with rfl | rfl
        · exact hcells j hj (hjt.trans ht)
        · exact hcells' j hj (hjt.trans ht)
      obtain ⟨-, -, -, -, -, -, -, -, -, hrow, hone⟩ :=
        branchT5_of_alignedConstant hd hg hCd hstat hunit hdag hwin hY hbridge cc
          hexact (hsearch hguard.1) hbaseCheckpoint hguard hout hread cert hmu
          (by rw [hs]; exact hbaseCursor) hentry hcont w
      exact ⟨.t5, hrules', hrow, by simpa using hone⟩
  | t6 =>
      have ht : S.base + max (H : ℤ) c.h ≤ run.queryScale := by
        simpa only [selectorStep, hselected] using hreadBoundRun
      have hread := hreadAt _ ht
      simp [selectorStep, hselected] at hout
      subst S'
      have hrow := branchT6Row (c := c) hd hg hetaProfBar hstat hunit hexact
        (hterminal hguard.1) hguard hread w
      have hone := PotentialRow.oneStepPotential w (hdet _ _ hjbase (by omega) ht) hrow
      refine ⟨.t6, hrules', hrow, ?_⟩
      simp only [if_neg (by decide : TransitionRule.t6 ≠ .t5), transitionCharge] at hone ⊢
      linarith only [hone]
  | t7 => simp [selectorStep, hselected] at hout

end

end Homogenization.HighContrast.Selection
