/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Terminal
import HCPoly.Provider.Selection.TerminalScales
import HCPoly.Provider.Selection.TerminalOutcome
import HCPoly.Provider.Selection.Enclosure
import HCPoly.Provider.Selection.SourceAccount

/-!
# Assembly of the terminal selector tuple

An actual terminal run, its preserved terminal invariant, and the execution
window geometry determine the returned block, witness, grid, and two scales.
The auxiliary multiplier used to establish definedness belongs only to the
proof; the source account is then quantified at the requested source constant.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar CdSel Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar CdSel
  Khop Ctr Ltr}
variable {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}

/-- The terminal outcome of the actual capped run supplies the complete tuple
and its source account at the independently requested source constant. -/
theorem selectionRun_terminal_tuple (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hetaProfBar : etaProfBar ≤ 1)
    (hH : 4 ≤ H)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {source : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K source)
    {Lam : ℝ} (hLamEq : Lam = Real.logb 3 (2 + aspectRatio E))
    {jdag Mexec r0 : ℤ}
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jdag Mexec)
    (hMexec : Mexec = jdag + ⌈cc.Cexec * Lam⌉)
    (hstart : jdag + ⌈cc.B * Lam⌉ ≤ r0)
    (hr0 : (r0 : ℝ) ≤ (jdag : ℝ) + cc.CR * Lam)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) (T : State d)
    (hout : (selectionRun cc P jdag Lam r0 A0 hcen hnl).outcome =
      RunOutcome.terminal T)
    (hcount : ((selectionRun cc P jdag Lam r0 A0 hcen hnl).transitionCount : ℝ) ≤
      cc.CN * Lam)
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jdag T)
    (hterminal : TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew
      c.etaX jdag T)
    (hcandidate : ∀ E0 : BlockMat d, T.candidate = some E0 →
      IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0)
    {Yaux : CoeffSpace d → ℝ}
    (hYaux : IsWindowMultiplier P g E Psi K CdSel jdag Mexec Yaux)
    {Cd Arad Agrid : ℝ} (hCd : 1 ≤ Cd)
    (hArad : Arad = radiusExponent c.chop cc.CN)
    (hAgrid : Agrid = gridExponent d c.chop cc.CN) :
    ∃ (E0 : BlockMat d) (m0 q : Mat d) (s t : ℤ),
      IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0 ∧
        m0 = canonicalMetric E0 ∧ q = roundedGrid jdag m0 ∧
        t = s + (H : ℤ) ∧
      (jdag + ⌈cc.B * Lam⌉ ≤ s ∧
        (t : ℝ) ≤ (jdag : ℝ) + cc.Csel * Lam ∧
        witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad ∧
        gridRatio q 1 ≤ (2 + aspectRatio E) ^ Agrid) ∧
      ((∀ k : ℤ, jdag ≤ k → k ≤ t →
          adaptedCell q k ⊆ centeredCube d Mexec) ∧
        (∀ k : ℤ, k < jdag → ∀ v : ℤ, v = s ∨ v = t →
          ∀ z ∈ containedCenters q k v,
            adaptedCellTranslate q k z ⊆ centeredCube d Mexec)) ∧
      (BlockMatLoewnerLE (blockScale (1 - epsCal) E0)
            (adaptedMean P q s) ∧
        BlockMatLoewnerLE (adaptedMean P q s)
            (blockScale (1 + epsCal) E0) ∧
        adaptedDetRoot P q s < (1 + c.deltaTerm) * adaptedDetRoot P q t ∧
        linearDrift P (initExpRhoDr g) q jdag s +
            linearDrift P (initExpRhoDr g) q jdag t ≤ etaDr) ∧
      (portableHistory P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) q jdag s ≤ ENNReal.ofReal c.etaIn ∧
        portableProfile P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) q jdag s t ≤ ENNReal.ofReal c.etaOut ∧
        portableHistory P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) q jdag t ≤ ENNReal.ofReal c.Cport *
              portableProfile P (initExpQ d g : ℝ) (initExpA g)
                (initExpRhoMax d g) q jdag s t ∧
        ENNReal.ofReal c.Cport *
            portableProfile P (initExpQ d g : ℝ) (initExpA g)
              (initExpRhoMax d g) q jdag s t ≤ ENNReal.ofReal c.epsSt ∧
        centeredHistory P (initExpQ d g : ℝ) (initExpRhoMax d g) q jdag t ≤
          ENNReal.ofReal c.epsSt) ∧
      ∀ Y : CoeffSpace d → ℝ,
        IsWindowMultiplier P g E Psi K Cd jdag Mexec Y →
          IsWindowedSourceFields P g Cd E jdag m0 s t Y ∧
            eLpNorm
                (belowStartSup (initExpRhoMax d g) q jdag t
                  (fun k => containedCenters q k t) (adaptedMean P q t))
                (ENNReal.ofReal (initExpQ d g : ℝ)) P ≤
              ENNReal.ofReal
                (initGridConst Cd g E m0 *
                  (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ)))) := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hPi : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hLam : 1 ≤ Lam := by
    rw [hLamEq]
    exact ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hceil : (0 : ℤ) ≤ ⌈cc.B * Lam⌉ :=
    Int.ceil_nonneg (mul_nonneg cc.B_pos.le (le_trans zero_le_one hLam))
  have hj0 : jdag ≤ r0 := by omega
  obtain ⟨E0, hcand, hm0, -, -⟩ := hterminal.2.2.2.2.2
  obtain ⟨hE0s, hE0p⟩ := hcandidate E0 hcand
  have hm0p : T.mu.PosDef := by
    rw [hm0]
    exact ShortHop.posDef_canonicalMetric (posDef_toFullBlockMat hE0s hE0p)
  have hq : IsRoundedGrid jdag T.q :=
    ⟨ShortHop.kZero_le_of_isCoupledWindow hwin, T.mu, hm0p, hexact.1⟩
  have hscales := selectionRun_terminal_scales hd cc hPi hLamEq hwin hstart
    hr0 hMexec A0 hcen hnl T hout hcount hYaux
  have henc := selectionRun_terminal_enclosure hd cc hLam hwin hj0 hr0 hMexec
    A0 hcen hnl T hout hYaux
  have hdef := selectionRun_terminal_definedness_and_mean_order hd hg cc hstat
    hdag.refBlock_isSymm hLam hwin hj0 hr0 hMexec A0 hcen hnl T hout hYaux
  have hjbase : jdag ≤ T.base := by omega
  have hjterm : jdag ≤ T.base + (H : ℤ) := by omega
  have htermPos : Book.Ch02.BlockPosDef
      (adaptedMean P T.q (T.base + (H : ℤ))) :=
    (hdef.1 (T.base + (H : ℤ)) hjterm le_rfl).2.1
  have hroot : 0 < adaptedDetRoot P T.q (T.base + (H : ℤ)) :=
    ShortHop.detRoot_pos (posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P T.q (T.base + (H : ℤ))) htermPos)
  have houtRaw :
      (runCapped P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jdag c.h c.chop c.l0 H c.etaReady c.etaPre
        c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
        (initialState r0 A0 hcen hnl)).outcome = RunOutcome.terminal T := by
    simpa only [selectionRun] using hout
  have hpass := runCapped_terminal_detRoot_pass P (initExpQ d g : ℝ)
    (initExpA g) (initExpRhoMax d g) (initExpRhoDr g) jdag c.h c.chop c.l0 H
    c.etaReady c.etaPre c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl) T houtRaw hroot
  have hphase := terminal_phase_outputs (c := c) hd hg hetaProfBar hH hstat
    hunit hE0s hE0p hcand hq hexact hterminal
    (fun j hj ht => (hdef.1 j hj ht).1)
    (fun j hj ht => (hdef.1 j hj ht).2.1)
    (fun j hj ht => (hdef.1 j hj ht).2.2) hdef.2 hpass
  refine ⟨E0, T.mu, T.q, T.base, T.base + (H : ℤ), hE0s, hE0p, hm0,
    hexact.1, rfl, ?_, henc, hphase.1, hphase.2, ?_⟩
  · exact ⟨hscales.1,
      by simpa only [Int.cast_add] using hscales.2.1,
      by simpa only [hArad] using hscales.2.2.1,
      by simpa only [hAgrid] using hscales.2.2.2⟩
  · intro Y hY
    exact selection_source_account hg hdag hCd hwin hE0s hE0p hm0 hexact.1
      hjbase (by omega) henc.1 henc.2 hY

end

end Homogenization.HighContrast.Selection
