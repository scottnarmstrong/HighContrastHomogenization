/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TerminalGeometry
import HCPoly.Provider.Selection.RunGeometry
import HCPoly.Provider.Selection.RunBounds
import HCPoly.Provider.Selection.TransitionTraceBounds
import HCPoly.Provider.Selection.Cutoff

/-!
# Terminal scales of the selector

The terminal trace records enough geometry to convert its successful path
steps into polynomial witness and grid bounds.  Independently, monotonicity of
the state base and the query budget place the returned pair of scales between
the initialized checkpoint and the selected upper cutoff.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
variable {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}

private theorem selectorStep_next_base_mono
    {P : Measure (CoeffSpace d)} {Q a rhoMax rhoDr : ℝ} {jStar h : ℤ}
    {chop : ℝ} {l0 H : ℕ} {etaReady etaPre deltaShort deltaTerm : ℝ}
    {S S' : State d} (hh : 0 ≤ h) (hbase : S.base ≤ S.cursor)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm S).outcome = StepOutcome.next S') :
    S.base ≤ S'.base ∧ S'.base ≤ S'.cursor := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S <;>
    simp [selectorStep, hrule] at hout
  all_goals subst S'
  all_goals simp [advanceCursor, hopState]
  all_goals omega

private theorem runCapped_terminal_base_mono
    {P : Measure (CoeffSpace d)} {Q a rhoMax rhoDr : ℝ} {jStar h : ℤ}
    {chop : ℝ} {l0 H fuel : ℕ} {etaReady etaPre deltaShort deltaTerm : ℝ}
    {S T : State d} (hh : 0 ≤ h) (hbase : S.base ≤ S.cursor)
    (hterminal : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm fuel S).outcome = RunOutcome.terminal T) :
    S.base ≤ T.base := by
  induction fuel generalizing S with
  | zero =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | next S' => simp [runCapped, hout] at hterminal
      | terminal state =>
          simp [runCapped, hout] at hterminal
          subst T
          rw [selectorStep_terminal_state P Q a rhoMax rhoDr jStar h chop l0 H
            etaReady etaPre deltaShort deltaTerm S state hout]
  | succ fuel ih =>
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          simp [runCapped, hout] at hterminal
          subst T
          rw [selectorStep_terminal_state P Q a rhoMax rhoDr jStar h chop l0 H
            etaReady etaPre deltaShort deltaTerm S state hout]
      | next S' =>
          simp only [runCapped, hout] at hterminal
          have hstep := selectorStep_next_base_mono hh hbase hout
          exact hstep.1.trans (ih hstep.2 hterminal)

/-- An actual terminal trace whose transition count has the printed linear
bound has the polynomial witness-eccentricity and rounded-grid bounds. -/
theorem selectionRun_terminal_polynomial_bounds (hd : 2 ≤ d)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Lam : ℝ} {jStar Mexec r0 : ℤ}
    (hPi : 1 ≤ aspectRatio E)
    (hLam : Lam = Real.logb 3 (2 + aspectRatio E))
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    (hj0 : jStar ≤ r0) (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (T : State d)
    (hterminal : (selectionRun cc P jStar Lam r0 A0 hcen hnl).outcome =
      RunOutcome.terminal T)
    (hcount : ((selectionRun cc P jStar Lam r0 A0 hcen hnl).transitionCount : ℝ) ≤
      cc.CN * Lam)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar Mexec Y) :
    witnessEccentricity T.mu ≤
        (2 + aspectRatio E) ^ radiusExponent c.chop cc.CN ∧
      gridRatio T.q 1 ≤
        (2 + aspectRatio E) ^ gridExponent d c.chop cc.CN := by
  let : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hLamOne : 1 ≤ Lam := by
    rw [hLam]
    exact ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hterminalRaw :
      (runCapped P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.h c.chop c.l0 H c.etaReady c.etaPre
        c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
        (initialState r0 A0 hcen hnl)).outcome = RunOutcome.terminal T := by
    simpa only [selectionRun] using hterminal
  have hmem : T ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states :=
    runCapped_terminal_state_mem P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
      (initialState r0 A0 hcen hnl) T hterminalRaw
  have hgeom := selectionRun_state_geometry hd cc hLamOne hwin hj0 hr0 hMexec
    A0 hcen hnl hY T hmem
  rcases hgeom with ⟨-, -, -, hmu, hgrid, hproj, -, -⟩
  have hlast := runCapped_terminal_getLast? P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
    c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl) T hterminalRaw
  have hstageNat := (runCapped_last_stage_le P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
    c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl) T (by simp [initialState]) hlast).1
  have hcountRaw :
      ((runCapped P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.h c.chop c.l0 H c.etaReady c.etaPre
        c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
        (initialState r0 A0 hcen hnl)).transitionCount : ℝ) ≤ cc.CN * Lam := by
    simpa only [selectionRun] using hcount
  have hstageRun : (T.stage : ℝ) ≤
      ((runCapped P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.h c.chop c.l0 H c.etaReady c.etaPre
        c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
        (initialState r0 A0 hcen hnl)).transitionCount : ℝ) := by
    exact_mod_cast hstageNat
  have hstage : (T.stage : ℝ) ≤ cc.CN * Lam := hstageRun.trans hcountRaw
  have hproj' : projDist 1 T.mu ≤ c.chop * (T.stage : ℝ) := by
    simpa only [mul_comm] using hproj
  have hecc := witnessEccentricity_le_rpow_of_hopCount (by omega : 1 ≤ d)
    hmu c.chop_pos.le hPi hLam hproj' hstage
  refine ⟨hecc, ?_⟩
  rw [hgrid]
  exact gridRatio_roundedGrid_one_le_rpow hd
    (ShortHop.kZero_le_of_isCoupledWindow hwin) hmu hPi hecc

/-- A terminal trace returns its lower scale beyond the initialized checkpoint
and its upper scale below the selected query cutoff. -/
theorem selectionRun_terminal_scale_bounds
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    (P : Measure (CoeffSpace d)) {Lam : ℝ} (hLam : 1 ≤ Lam)
    {jStar r0 : ℤ} (hstart : jStar + ⌈cc.B * Lam⌉ ≤ r0)
    (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (T : State d)
    (hterminal : (selectionRun cc P jStar Lam r0 A0 hcen hnl).outcome =
      RunOutcome.terminal T) :
    jStar + ⌈cc.B * Lam⌉ ≤ T.base ∧
      ((T.base + (H : ℤ)) : ℝ) ≤ (jStar : ℝ) + cc.Csel * Lam := by
  have hterminalRaw :
      (runCapped P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.h c.chop c.l0 H c.etaReady c.etaPre
        c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
        (initialState r0 A0 hcen hnl)).outcome = RunOutcome.terminal T := by
    simpa only [selectionRun] using hterminal
  have hbase : r0 ≤ T.base :=
    runCapped_terminal_base_mono (le_trans (by norm_num) c.one_le_h)
      (by simp [initialState]) hterminalRaw
  have htquery := runCapped_terminal_scale_le_queryScale hterminalRaw
  have htqueryReal : ((T.base + (H : ℤ)) : ℝ) ≤
      ((selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale : ℝ) := by
    exact_mod_cast htquery
  exact ⟨hstart.trans hbase, htqueryReal.trans
    (selectionRun_queryScale_le cc P jStar hLam r0 A0 hcen hnl hr0).2⟩

/-- The actual terminal run satisfies all four terminal scale conclusions. -/
theorem selectionRun_terminal_scales (hd : 2 ≤ d)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Lam : ℝ} {jStar Mexec r0 : ℤ}
    (hPi : 1 ≤ aspectRatio E)
    (hLam : Lam = Real.logb 3 (2 + aspectRatio E))
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    (hstart : jStar + ⌈cc.B * Lam⌉ ≤ r0)
    (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (T : State d)
    (hterminal : (selectionRun cc P jStar Lam r0 A0 hcen hnl).outcome =
      RunOutcome.terminal T)
    (hcount : ((selectionRun cc P jStar Lam r0 A0 hcen hnl).transitionCount : ℝ) ≤
      cc.CN * Lam)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar Mexec Y) :
    jStar + ⌈cc.B * Lam⌉ ≤ T.base ∧
      ((T.base + (H : ℤ)) : ℝ) ≤ (jStar : ℝ) + cc.Csel * Lam ∧
      witnessEccentricity T.mu ≤
        (2 + aspectRatio E) ^ radiusExponent c.chop cc.CN ∧
      gridRatio T.q 1 ≤
        (2 + aspectRatio E) ^ gridExponent d c.chop cc.CN := by
  have hLamOne : 1 ≤ Lam := by
    rw [hLam]
    exact ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hceil : (0 : ℤ) ≤ ⌈cc.B * Lam⌉ :=
    Int.ceil_nonneg (mul_nonneg cc.B_pos.le (le_trans zero_le_one hLamOne))
  have hj0 : jStar ≤ r0 := (by omega : jStar ≤ jStar + ⌈cc.B * Lam⌉).trans hstart
  have hs := selectionRun_terminal_scale_bounds cc P hLamOne hstart hr0
    A0 hcen hnl T hterminal
  have hp := selectionRun_terminal_polynomial_bounds hd cc hPi hLam hwin hj0
    hr0 hMexec A0 hcen hnl T hterminal hcount hY
  exact ⟨hs.1, hs.2, hp.1, hp.2⟩

end

end Homogenization.HighContrast.Selection
