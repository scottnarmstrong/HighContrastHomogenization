/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.State
import HCPoly.Provider.Selection.Transitions
import HCPoly.Provider.Selection.TransitionGuards
import HCPoly.Provider.Selection.CappedRun
import HCPoly.Provider.Selection.RunBounds
import HCPoly.Provider.Selection.EnclosureGeometry
import HCPoly.Provider.Selection.RunGeometry
import HCPoly.Provider.Transport.WindowDefinedness

/-!
# The terminal enclosure of the capped selector

The terminal state and the whole capped trace are fixed before a multiplier is
quantified.  Geometry of the trace encloses the terminal adapted-cell tower;
the exact terminal-family identity then supplies the below-start cells.  Only
after this enclosure is established is a multiplier used to derive finiteness,
positivity, centered-moment finiteness, and the aligned mean order.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
variable {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}

/-! ## The two terminal enclosure clauses -/

/-- A terminal outcome of the actual capped run satisfies both clauses of the
preassigned-window enclosure.  The run and terminal state occur before the
multiplier binder. -/
theorem selectionRun_terminal_enclosure (hd : 2 ≤ d)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Lam : ℝ} {jStar Mexec r0 : ℤ}
    (hLam : 1 ≤ Lam)
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    (hj0 : jStar ≤ r0) (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (terminalState : State d)
    (hterminal : (selectionRun cc P jStar Lam r0 A0 hcen hnl).outcome =
      RunOutcome.terminal terminalState)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar Mexec Y) :
    (∀ k : ℤ, jStar ≤ k → k ≤ terminalState.base + (H : ℤ) →
        adaptedCell terminalState.q k ⊆ centeredCube d Mexec) ∧
      (∀ k : ℤ, k < jStar → ∀ v : ℤ,
        v = terminalState.base ∨ v = terminalState.base + (H : ℤ) →
        ∀ z ∈ containedCenters terminalState.q k v,
          adaptedCellTranslate terminalState.q k z ⊆ centeredCube d Mexec) := by
  letI : NeZero d := ⟨by omega⟩
  have hmem : terminalState ∈
      (selectionRun cc P jStar Lam r0 A0 hcen hnl).states := by
    exact runCapped_terminal_state_mem P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
      (initialState r0 A0 hcen hnl) terminalState
      (by simpa only [selectionRun] using hterminal)
  have hgeom := selectionRun_state_geometry hd cc hLam hwin hj0 hr0 hMexec
    A0 hcen hnl hY terminalState hmem
  rcases hgeom with ⟨-, hbase, -, hmu, hgrid, -, -, hcells⟩
  have htquery : terminalState.base + (H : ℤ) ≤
      (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale := by
    exact runCapped_terminal_scale_le_queryScale
      (by simpa only [selectionRun] using hterminal)
  have hjround := ShortHop.kZero_le_of_isCoupledWindow hwin
  have hq : terminalState.q.PosDef := by
    rw [hgrid]
    exact Recurrence.posDef_roundedGrid hjround hmu
  have hwhole : ∀ k : ℤ, jStar ≤ k → k ≤ terminalState.base + (H : ℤ) →
      adaptedCell terminalState.q k ⊆ centeredCube d Mexec := by
    intro k hjk hkt
    exact hcells k hjk (hkt.trans htquery)
  exact terminal_enclosure_of_adaptedCell_enclosure hq hbase (by omega) hwhole

/-! ## Definedness and aligned mean order -/

/-- Every grid visited by the capped run has finite positive-definite means,
finite centered moments, and decreasing means throughout the queried range. -/
theorem selectionRun_states_definedness_and_mean_order (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) {Ψ : ℝ → ℝ}
    {K Lam : ℝ} {jStar Mexec r0 : ℤ} (hLam : 1 ≤ Lam)
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    (hj0 : jStar ≤ r0) (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar Mexec Y) :
    (∀ S' ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states,
      ∀ j : ℤ, jStar ≤ j →
        j ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale →
          HasFiniteAdaptedMean P S'.q j ∧
            Book.Ch02.BlockPosDef (adaptedMean P S'.q j) ∧
            centeredMoment P (initExpQ d g : ℝ) S'.q j ≠ ⊤) ∧
      (∀ S' ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states,
        ∀ j T : ℤ, jStar ≤ j → j ≤ T →
          T ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale →
            BlockMatLoewnerLE (adaptedMean P S'.q T)
              (adaptedMean P S'.q j)) := by
  letI : NeZero d := ⟨by omega⟩
  have hQ : 1 ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast le_trans (by omega : 1 ≤ 2) (two_le_initExpQ hg)
  have hstate : ∀ S' ∈
      (selectionRun cc P jStar Lam r0 A0 hcen hnl).states,
      (∀ j : ℤ, jStar ≤ j →
        j ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale →
          HasFiniteAdaptedMean P S'.q j ∧
            Book.Ch02.BlockPosDef (adaptedMean P S'.q j) ∧
            centeredMoment P (initExpQ d g : ℝ) S'.q j ≠ ⊤) ∧
        (∀ j T : ℤ, jStar ≤ j → j ≤ T →
          T ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale →
            BlockMatLoewnerLE (adaptedMean P S'.q T)
              (adaptedMean P S'.q j)) := by
    intro S' hS'
    have hgeom := selectionRun_state_geometry hd cc hLam hwin hj0 hr0 hMexec
      A0 hcen hnl hY S' hS'
    rcases hgeom with ⟨-, -, -, hmu, hgrid, -, -, hcells⟩
    have hcont : ∀ r : Mat d,
        r = roundedGrid jStar S'.mu ∨ r = roundedGrid jStar S'.mu →
        ∀ j : ℤ, jStar ≤ j →
          j ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale →
            adaptedCell r j ⊆ centeredCube d Mexec := by
      intro r hr j hj hjq
      rcases hr with rfl | rfl
      all_goals rw [← hgrid]
      all_goals exact hcells j hj hjq
    have hdef := Transport.definedness_of_isWindowMultiplier hd hP hE hQ hwin hY
      hmu hmu hcont
    constructor
    · intro j hj hjq
      simpa only [← hgrid] using
        hdef.1 (roundedGrid jStar S'.mu) (Or.inl rfl) j hj hjq
    · intro j T hj hjT hTq
      simpa only [← hgrid] using
        hdef.2 (roundedGrid jStar S'.mu) (Or.inl rfl) j T hj hjT hTq
  exact ⟨fun S' hS' => (hstate S' hS').1,
    fun S' hS' => (hstate S' hS').2⟩

/-- Once the terminal run and its enclosure are fixed, every multiplier of the
preassigned window makes the terminal tower finite and positive definite, with
finite centered moments and decreasing annealed means. -/
theorem selectionRun_terminal_definedness_and_mean_order (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) {Ψ : ℝ → ℝ}
    {K Lam : ℝ} {jStar Mexec r0 : ℤ} (hLam : 1 ≤ Lam)
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    (hj0 : jStar ≤ r0) (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (terminalState : State d)
    (hterminal : (selectionRun cc P jStar Lam r0 A0 hcen hnl).outcome =
      RunOutcome.terminal terminalState)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar Mexec Y) :
    (∀ j : ℤ, jStar ≤ j → j ≤ terminalState.base + (H : ℤ) →
        HasFiniteAdaptedMean P terminalState.q j ∧
          Book.Ch02.BlockPosDef (adaptedMean P terminalState.q j) ∧
          centeredMoment P (initExpQ d g : ℝ) terminalState.q j ≠ ⊤) ∧
      (∀ j T : ℤ, jStar ≤ j → j ≤ T →
        T ≤ terminalState.base + (H : ℤ) →
          BlockMatLoewnerLE (adaptedMean P terminalState.q T)
            (adaptedMean P terminalState.q j)) := by
  letI : NeZero d := ⟨by omega⟩
  have henc := selectionRun_terminal_enclosure hd cc hLam hwin hj0 hr0 hMexec
    A0 hcen hnl terminalState hterminal hY
  have hmem : terminalState ∈
      (selectionRun cc P jStar Lam r0 A0 hcen hnl).states := by
    exact runCapped_terminal_state_mem P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
      (initialState r0 A0 hcen hnl) terminalState
      (by simpa only [selectionRun] using hterminal)
  have hgeom := selectionRun_state_geometry hd cc hLam hwin hj0 hr0 hMexec
    A0 hcen hnl hY terminalState hmem
  rcases hgeom with ⟨-, -, -, hmu, hgrid, -, -, -⟩
  have hQ : 1 ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast le_trans (by omega : 1 ≤ 2) (two_le_initExpQ hg)
  have hcont : ∀ r : Mat d,
      r = roundedGrid jStar terminalState.mu ∨
        r = roundedGrid jStar terminalState.mu →
      ∀ j : ℤ, jStar ≤ j → j ≤ terminalState.base + (H : ℤ) →
        adaptedCell r j ⊆ centeredCube d Mexec := by
    intro r hr j hj hjs
    rcases hr with rfl | rfl
    all_goals rw [← hgrid]
    all_goals exact henc.1 j hj hjs
  have hdef := Transport.definedness_of_isWindowMultiplier hd hP hE hQ hwin hY
    hmu hmu hcont
  refine ⟨?_, ?_⟩
  · intro j hj hjs
    simpa only [← hgrid] using
      hdef.1 (roundedGrid jStar terminalState.mu) (Or.inl rfl) j hj hjs
  · intro j T hj hjT hTs
    simpa only [← hgrid] using
      hdef.2 (roundedGrid jStar terminalState.mu) (Or.inl rfl) j T hj hjT hTs

end

end Homogenization.HighContrast.Selection
