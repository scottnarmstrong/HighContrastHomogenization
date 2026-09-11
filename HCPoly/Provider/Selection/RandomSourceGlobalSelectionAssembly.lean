/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Frozen.RandomSourceWindow
import HCPoly.Provider.Selection.AlignedSelectionConstants
import HCPoly.Provider.Selection.PreLaw
import HCPoly.Provider.Selection.ExecutionWindow
import HCPoly.Provider.Selection.InitialEntry
import HCPoly.Provider.Selection.StrictTermination
import HCPoly.Provider.Selection.TerminalTuple

/-!
# Global random-source selection

The aligned transport and shifted-drift providers feed the capped selector.
Its strict termination and terminal invariant produce the complete selected
window and source account.  There are no definitions in this file.
-/

open MeasureTheory
open Homogenization
open Homogenization.HighContrast
open Homogenization.HighContrast.Selection

theorem Homogenization.HighContrast.Selection.random_source_global_selection_assembly
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (cStar : ℝ) (hcStar : 0 < cStar)
    (epsCal : ℝ) (hepsCalLo : 0 < epsCal) (hepsCalHi : epsCal ≤ 1)
    (etaDr : ℝ) (hetaDrLo : 0 < etaDr) (hetaDrHi : etaDr ≤ 1)
    (etaProfBar : ℝ) (hetaProfLo : 0 < etaProfBar) (hetaProfHi : etaProfBar ≤ 1)
    (deltaDetBar : ℝ) (hdeltaDetLo : 0 < deltaDetBar)
    (hdeltaDetHi : deltaDetBar ≤ 1)
    (H : ℕ) (hH : 4 ≤ H) :
    ∀ Cd : ℝ, 1 ≤ Cd →
    ∃ Arad Agrid : ℝ, 0 < Arad ∧ 0 < Agrid ∧
      ∃ etaIn etaOut epsSt deltaTerm : ℝ,
        0 < etaIn ∧ 0 < etaOut ∧ 0 < epsSt ∧ 0 < deltaTerm ∧
        ∃ Cport : ℝ, 1 ≤ Cport ∧
          -- the output constants meet the downstream caps
          max (max etaIn etaOut) epsSt ≤ etaProfBar ∧ deltaTerm ≤ deltaDetBar ∧
          ∀ Bmin : ℝ, 1 ≤ Bmin →
          ∃ B Cexec Csel : ℝ, Bmin ≤ B ∧ 0 < Cexec ∧ 0 < Csel ∧
            -- the cutoff inequalities for the buffer multiple
            1 < Homogenization.HighContrast.initExpRhoDr g * B / 2 ∧
            (Homogenization.HighContrast.initExpQ d g : ℝ) <
              Homogenization.HighContrast.initExpA g * B / 2 ∧
            ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
              (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
              (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
              MeasureTheory.IsProbabilityMeasure P →
              HCPoly.Frozen.IsStationaryLaw P →
              HCPoly.Frozen.IsUnitRangeLaw P →
              HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
              ∀ Lam : ℝ,
                Lam = Real.logb 3 (2 + Homogenization.HighContrast.aspectRatio E) →
                ∀ jdag Mexec : ℤ,
                  jdag =
                    Homogenization.HighContrast.coupledExecBurn d
                      (Homogenization.HighContrast.initExpQ d g : ℝ) K Cexec Lam →
                  Mexec = jdag + ⌈Cexec * Lam⌉ →
        -- the execution window: the window has
        -- positive height, the pair is coupled, and the burn is bounded.  These
        -- are established before a multiplier is constructed, which is what
        -- makes the multiplier of the window lemma available at this pair.
        (1 ≤ Mexec - jdag ∧
          Homogenization.HighContrast.IsCoupledWindow d
            (Homogenization.HighContrast.initExpQ d g : ℝ) K jdag Mexec ∧
          (jdag : ℝ) ≤
            (Homogenization.HighContrast.sourceBurn d
                (Homogenization.HighContrast.initExpQ d g : ℝ) K : ℝ) + 1 +
              ((d : ℝ) * (1 + Cexec * Lam) +
                  16 * ((d : ℝ) + 1) ^ 2 *
                    Real.logb 3 (Homogenization.HighContrast.growthBar K)) /
                (4 * (d : ℝ) + 3)) ∧
        -- the law-determined terminal tuple
        ∃ (E0 : Homogenization.BlockMat d) (m0 q : Homogenization.Mat d) (s t : ℤ),
          Homogenization.IsSymmetricBlockMat E0 ∧
            Homogenization.Book.Ch02.BlockPosDef E0 ∧
            m0 = Homogenization.HighContrast.canonicalMetric E0 ∧
            q = Homogenization.HighContrast.roundedGrid jdag m0 ∧
            t = s + (H : ℤ) ∧
          -- the selected scales `e.global.selection.scales`, the eccentricity
          -- `e.global.selection.eccentricity`, and the companion grid ratio
          (jdag + ⌈B * Lam⌉ ≤ s ∧
            (t : ℝ) ≤ (jdag : ℝ) + Csel * Lam ∧
            Homogenization.HighContrast.witnessEccentricity m0 ≤
              (2 + Homogenization.HighContrast.aspectRatio E) ^ Arad ∧
            Homogenization.HighContrast.gridRatio q 1 ≤
              (2 + Homogenization.HighContrast.aspectRatio E) ^ Agrid) ∧
          -- every cell read by the selection lies in the execution window
          ((∀ k : ℤ, jdag ≤ k → k ≤ t →
              Homogenization.HighContrast.adaptedCell q k ⊆
                Homogenization.HighContrast.centeredCube d Mexec) ∧
            (∀ k : ℤ, k < jdag → ∀ v : ℤ, v = s ∨ v = t →
              ∀ z ∈ Homogenization.HighContrast.containedCenters q k v,
                Homogenization.HighContrast.adaptedCellTranslate q k z ⊆
                  Homogenization.HighContrast.centeredCube d Mexec)) ∧
          -- the calibration and determinant closeness
          -- `e.global.selection.calibration`, and the drift sum at the two
          -- endpoints
          (Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.blockScale (1 - epsCal) E0)
              (Homogenization.HighContrast.adaptedMean P q s) ∧
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.adaptedMean P q s)
              (Homogenization.HighContrast.blockScale (1 + epsCal) E0) ∧
            Homogenization.HighContrast.adaptedDetRoot P q s <
              (1 + deltaTerm) * Homogenization.HighContrast.adaptedDetRoot P q t ∧
            Homogenization.HighContrast.linearDrift P
                  (Homogenization.HighContrast.initExpRhoDr g) q jdag s +
                Homogenization.HighContrast.linearDrift P
                  (Homogenization.HighContrast.initExpRhoDr g) q jdag t ≤
              etaDr) ∧
          -- the retained histories and profile of `e.global.selection.profile`,
          -- and the centered maximum at the terminal generation
          (Homogenization.HighContrast.portableHistory P
                (Homogenization.HighContrast.initExpQ d g : ℝ)
                (Homogenization.HighContrast.initExpA g)
                (Homogenization.HighContrast.initExpRhoMax d g) q jdag s ≤
              ENNReal.ofReal etaIn ∧
            Homogenization.HighContrast.portableProfile P
                (Homogenization.HighContrast.initExpQ d g : ℝ)
                (Homogenization.HighContrast.initExpA g)
                (Homogenization.HighContrast.initExpRhoMax d g) q jdag s t ≤
              ENNReal.ofReal etaOut ∧
            Homogenization.HighContrast.portableHistory P
                (Homogenization.HighContrast.initExpQ d g : ℝ)
                (Homogenization.HighContrast.initExpA g)
                (Homogenization.HighContrast.initExpRhoMax d g) q jdag t ≤
              ENNReal.ofReal Cport *
                Homogenization.HighContrast.portableProfile P
                  (Homogenization.HighContrast.initExpQ d g : ℝ)
                  (Homogenization.HighContrast.initExpA g)
                  (Homogenization.HighContrast.initExpRhoMax d g) q jdag s t ∧
            ENNReal.ofReal Cport *
                Homogenization.HighContrast.portableProfile P
                  (Homogenization.HighContrast.initExpQ d g : ℝ)
                  (Homogenization.HighContrast.initExpA g)
                  (Homogenization.HighContrast.initExpRhoMax d g) q jdag s t ≤
              ENNReal.ofReal epsSt ∧
            Homogenization.HighContrast.centeredHistory P
                (Homogenization.HighContrast.initExpQ d g : ℝ)
                (Homogenization.HighContrast.initExpRhoMax d g) q jdag t ≤
              ENNReal.ofReal epsSt) ∧
          -- the source account is read at the window's own multiplier, which
          -- is bound only here: the returned tuple above is determined by the
          -- law alone and reads no realization of it
          ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
            Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jdag
              Mexec Y →
          -- the localized source cells, the weighted source row, and the
          -- reference comparisons at the two endpoints
          Homogenization.HighContrast.IsWindowedSourceFields P g Cd E jdag m0 s t
              Y ∧
            -- the sharp below-start maximum at the terminal generation
            MeasureTheory.eLpNorm
                (Homogenization.HighContrast.belowStartSup
                  (Homogenization.HighContrast.initExpRhoMax d g) q jdag t
                  (fun k => Homogenization.HighContrast.containedCenters q k t)
                  (Homogenization.HighContrast.adaptedMean P q t))
                (ENNReal.ofReal (Homogenization.HighContrast.initExpQ d g : ℝ)) P ≤
              ENNReal.ofReal
                (Homogenization.HighContrast.initGridConst Cd g E m0 *
                  (3 : ℝ) ^
                    (-Homogenization.HighContrast.initExpRhoMax d g *
                      ((t : ℝ) - (jdag : ℝ))))
    := by
  intro Cd hCd
  have hQraw : (2 : ℝ) ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast two_le_initExpQ (d := d) (g := g) hg
  have hQ : (2 : ℝ) ≤ (initExpQ d g : ℝ) := by
    have hscaled : 2 * cStar ≤ (initExpQ d g : ℝ) * cStar :=
      mul_le_mul_of_nonneg_right hQraw hcStar.le
    nlinarith only [hscaled, hcStar]
  have hepsCalLo' : 0 < epsCal := by
    have hmin : 0 < min epsCal 1 := (lt_min_iff).2 ⟨hepsCalLo, zero_lt_one⟩
    rwa [min_eq_left hepsCalHi] at hmin
  have hetaDrLo' : 0 < etaDr := by
    have hmin : 0 < min etaDr 1 := (lt_min_iff).2 ⟨hetaDrLo, zero_lt_one⟩
    rwa [min_eq_left hetaDrHi] at hmin
  have hdeltaDetLo' : 0 < deltaDetBar := by
    have hmin : 0 < min deltaDetBar 1 :=
      (lt_min_iff).2 ⟨hdeltaDetLo, zero_lt_one⟩
    rwa [min_eq_left hdeltaDetHi] at hmin
  obtain ⟨Cd0, -, hwindow⟩ :=
    HCPoly.Frozen.random_source_window d hd g hg (initExpQ d g : ℝ) hQ
  let CdSel : ℝ := max Cd Cd0
  have hCdSel : 1 ≤ CdSel := hCd.trans (le_max_left _ _)
  obtain ⟨Khop, hKhop, hhop⟩ := exists_hopConstant hd 1
  obtain ⟨Ltr, Ctr, htransport, hbridgeAll⟩ :=
    exists_alignedTransportAndDriftConstant d hd g hg Khop hKhop
  obtain ⟨c, hchop, Chit, hinit, w, hcut⟩ := exists_globalSelection_preLaw
    d hd g hg epsCal etaDr etaProfBar deltaDetBar hepsCalLo' hetaDrLo'
    hetaProfLo hdeltaDetLo' H hH CdSel hCdSel Khop hKhop hhop Ltr Ctr htransport
  obtain ⟨ccRef⟩ := hcut 1 le_rfl
  let Arad : ℝ := radiusExponent c.chop ccRef.CN
  let Agrid : ℝ := gridExponent d c.chop ccRef.CN
  have hAradPos : 0 < Arad := by
    exact radiusExponent_pos c.chop_pos ccRef.CN_pos
  have hAgridPos : 0 < Agrid := by
    exact gridExponent_pos (by omega) c.chop_pos ccRef.CN_pos
  refine ⟨Arad, Agrid, hAradPos, hAgridPos, c.etaIn, c.etaOut, c.epsSt,
    c.deltaTerm, c.etaIn_pos, c.etaOut_pos, c.epsSt_pos, c.deltaTerm_pos,
    c.Cport, c.one_le_Cport, c.profile_caps, c.deltaTerm_le_deltaDetBar, ?_⟩
  intro Bmin hBmin
  obtain ⟨cc⟩ := hcut Bmin hBmin
  have hCN : cc.CN = ccRef.CN := by
    rw [cc.CN_eq, ccRef.CN_eq, cc.CF_eq, ccRef.CF_eq]
  have hArad : Arad = radiusExponent c.chop cc.CN := by
    dsimp only [Arad]
    rw [hCN]
  have hAgrid : Agrid = gridExponent d c.chop cc.CN := by
    dsimp only [Agrid]
    rw [hCN]
  refine ⟨cc.B, cc.Cexec, cc.Csel, cc.Bmin_le, cc.Cexec_pos, cc.Csel_pos,
    cc.rho_cutoff, cc.moment_cutoff, ?_⟩
  intro P E Psi K source hprob hstat hunit hdag Lam hLamEq jdag Mexec hjdag hMexec
  letI : IsProbabilityMeasure P := hprob
  letI : NeZero d := ⟨by omega⟩
  have hPi : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hLam : 1 ≤ Lam := by
    rw [hLamEq]
    exact Homogenization.HighContrast.ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hexec := execution_window_facts d g K cc.Cexec Lam cc.Cexec_pos hLam
    jdag Mexec hjdag hMexec
  refine ⟨hexec, ?_⟩
  have hwindowData := hwindow CdSel (le_max_right Cd Cd0) P E Psi K source
    hprob hstat hdag jdag Mexec hexec.2.1
  obtain ⟨Yaux, hYaux, -⟩ := hwindowData.2.2.2
  have hbridge := hbridgeAll CdSel hCdSel P E Psi K source hprob hstat hunit
    hdag jdag Mexec hexec.2.1 Yaux hYaux
  obtain ⟨r0, A0, hcen, hnl, hstart, hr0, -, -, -, hexact0, hfresh0,
      -, -, hroot0, hpotential0⟩ :=
    exists_initialSelectionEntry hd hg w hinit cc hstat hunit hdag hLamEq
      hexec.2.1 hMexec hYaux
  have htermination := selectionRun_strictly_terminates hd hg hCdSel hetaProfHi
    hstat hunit hdag hexec.2.1 hYaux hbridge w cc hLamEq hMexec hstart hr0
    hexact0 hfresh0 hroot0 hpotential0
  let run := selectionRun cc P jdag Lam r0 A0 hcen hnl
  let T := runFinalState run
  have hcount : (run.transitionCount : ℝ) ≤ cc.CN * Lam := by
    simpa only [run] using htermination.1
  have hout : run.outcome = RunOutcome.terminal T := by
    simpa only [run, T] using htermination.2.2
  have hceil0 : (0 : ℤ) ≤ ⌈cc.B * Lam⌉ :=
    Int.ceil_nonneg (mul_nonneg cc.B_pos.le (le_trans zero_le_one hLam))
  have hj0 : jdag ≤ r0 := by omega
  have hentry : cc.B * Real.logb 3 (2 + aspectRatio E) ≤
      (r0 : ℝ) - (jdag : ℝ) := by
    rw [← hLamEq]
    have hceil : cc.B * Lam ≤ ((⌈cc.B * Lam⌉ : ℤ) : ℝ) := Int.le_ceil _
    have hstartReal : (jdag : ℝ) + ((⌈cc.B * Lam⌉ : ℤ) : ℝ) ≤ (r0 : ℝ) := by
      exact_mod_cast hstart
    linarith only [hceil, hstartReal]
  have houtRaw :
      (runCapped P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jdag c.h c.chop c.l0 H c.etaReady c.etaPre
        c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
        (initialState r0 A0 hcen hnl)).outcome = RunOutcome.terminal T := by
    simpa only [run, selectionRun] using hout
  have hTmemRaw := runCapped_terminal_state_mem P (initExpQ d g : ℝ)
    (initExpA g) (initExpRhoMax d g) (initExpRhoDr g) jdag c.h c.chop c.l0 H
    c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl) T houtRaw
  have hTmem : T ∈ run.states := by
    simpa only [run, selectionRun] using hTmemRaw
  obtain ⟨hexactT, -, -, -, hphase, -⟩ := selectionRun_state_invariants hd hg
    hCdSel hstat hunit hdag hexec.2.1 hYaux hbridge cc hLam hj0 hr0 hMexec
    hexact0 hfresh0 hentry T (by simpa only [run] using hTmem)
  have hguard := runCapped_terminal_guard P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) jdag c.h c.chop c.l0 H c.etaReady
    c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl) T houtRaw
  have hterminal : TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew
      c.etaX jdag T ∧ ∀ E0 : BlockMat d, T.candidate = some E0 →
        IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0 := by
    rcases hphase with hfresh | hsearch | hterminal
    · exact False.elim (by cases hfresh.1.symm.trans hguard.1)
    · exact False.elim (by cases hsearch.1.symm.trans hguard.1)
    · exact hterminal
  exact selectionRun_terminal_tuple hd hg hetaProfHi hH cc hstat hunit hdag
    hLamEq hexec.2.1 hMexec hstart hr0 A0 hcen hnl T hout hcount hexactT
    hterminal.1 hterminal.2 hYaux hCd hArad hAgrid
