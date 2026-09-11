/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchHopData
import HCPoly.Provider.Selection.RunInvariantDefinedness

/-!
# One-step preservation for selector invariants

Each executable nonterminal rule preserves the exact state data and the
proof-only projective-hop prefix.  Rule T5 alone extends the prefix and renews
the history, drift, and terminal-candidate data.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- One actual nonterminal selector step preserves the full proof invariant. -/
theorem selectorStep_next_invariants (hd : 2 ≤ d)
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
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
          adaptedCell r j ⊆ centeredCube d M) →
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
    {r0 : ℤ} (hentry : z.B * Real.logb 3 (2 + aspectRatio E) ≤
      (r0 : ℝ) - (jStar : ℝ)) {S S' : State d}
    (hjbase : jStar ≤ S.base) (hbaseCursor : S.base ≤ S.cursor)
    (hbaseCheckpoint : S.base = S.checkpoint)
    (hout : (selectorStep P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm S).outcome = .next S')
    {Tquery : ℤ}
    (hreadBound : (selectorStep P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm S).readScale ≤ Tquery)
    (hnewFinite : HasFiniteAdaptedMean P S'.q S'.base)
    (hread : selectedRule P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H S = .t5 →
      FixedGridReadData (g := g) P jStar S (S.cursor + 2 * (c.l0 : ℤ)))
    (hcont : selectedRule P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
        c.deltaShort c.deltaTerm c.l0 H S = .t5 →
      ∀ r : Mat d, r = S.q ∨ r = S'.q → ∀ j : ℤ,
        jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
          adaptedCell r j ⊆ centeredCube d M)
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hhistory : stateHistory S ≤ ENNReal.ofReal c.etaIn)
    (hphase : FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar S ∨
      SearchInvariant c.h S ∨
      TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew c.etaX jStar S ∧
        ∀ E0 : BlockMat d, S.candidate = some E0 →
          IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0)
    (cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 S.stage)
    (hstartsZero : cert.starts 0 = r0)
    (hmu : cert.mus S.stage = S.mu) (hq : cert.grids S.stage = S.q)
    (hs : cert.starts S.stage = S.base)
    (hloss : S.prefixLoss = cert.completedLoss + detLoss P S.q S.base S.cursor)
    (hcertBridge : ∀ i : ℕ, i < S.stage →
      BlockMatLoewnerLE (blockScale (1 - cert.eta i)
        (adaptedMean P (cert.grids i) (cert.terminals i)))
        (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1))) ∧
      BlockMatLoewnerLE
        (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1)))
        (blockScale (1 + cert.eta i)
          (adaptedMean P (cert.grids i) (cert.terminals i))))
    (hstartsBound : ∀ i : ℕ, i ≤ S.stage → cert.starts i ≤ Tquery)
    (hterminalsBound : ∀ i : ℕ, i < S.stage → cert.terminals i ≤ Tquery)
    (hfinStarts : ∀ i : ℕ, i ≤ S.stage →
      HasFiniteAdaptedMean P (cert.grids i) (cert.starts i))
    (hfinTerminals : ∀ i : ℕ, i < S.stage →
      HasFiniteAdaptedMean P (cert.grids i) (cert.terminals i))
    (hcertEta : ∀ i : ℕ, i < S.stage → cert.eta i ≤ c.etaX) :
    ExactStateData P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) jStar S' ∧
      S'.base = S'.checkpoint ∧
      S'.cursor ≤ Tquery ∧
      stateHistory S' ≤ ENNReal.ofReal c.etaIn ∧
      (FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar S' ∨
        SearchInvariant c.h S' ∨
        TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew c.etaX jStar S' ∧
          ∀ E0 : BlockMat d, S'.candidate = some E0 →
            IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0) ∧
      ∃ cert' : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 S'.stage,
        cert'.mus S'.stage = S'.mu ∧ cert'.grids S'.stage = S'.q ∧
        cert'.starts S'.stage = S'.base ∧
        S'.prefixLoss = cert'.completedLoss + detLoss P S'.q S'.base S'.cursor ∧
        (∀ i : ℕ, i < S'.stage →
          BlockMatLoewnerLE (blockScale (1 - cert'.eta i)
            (adaptedMean P (cert'.grids i) (cert'.terminals i)))
            (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1))) ∧
          BlockMatLoewnerLE
            (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1)))
            (blockScale (1 + cert'.eta i)
              (adaptedMean P (cert'.grids i) (cert'.terminals i)))) ∧
        (∀ i : ℕ, i ≤ S'.stage → cert'.starts i ≤ Tquery) ∧
        (∀ i : ℕ, i < S'.stage → cert'.terminals i ≤ Tquery) ∧
        (∀ i : ℕ, i ≤ S'.stage →
          HasFiniteAdaptedMean P (cert'.grids i) (cert'.starts i)) ∧
        (∀ i : ℕ, i < S'.stage →
          HasFiniteAdaptedMean P (cert'.grids i) (cert'.terminals i)) ∧
        (∀ i : ℕ, i < S'.stage → cert'.eta i ≤ c.etaX) ∧
        cert'.starts 0 = r0 := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hh : 1 ≤ c.h := c.one_le_h
  have hl0 : (0 : ℤ) ≤ (c.l0 : ℤ) := by omega
  have hguard := selectedRule_guard P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
    c.deltaShort c.deltaTerm c.l0 H S
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
  have hadvance (v : ℤ) (hv : S.checkpoint ≤ v) (hvQuery : v ≤ Tquery)
      (hsearch' : SearchInvariant c.h (advanceCursor P S v .search none)) :=
    advanceCursor_next_invariants hv hvQuery hexact hbaseCheckpoint hhistory hsearch'
      cert hstartsZero hmu hq hs hloss hcertBridge hstartsBound hterminalsBound hfinStarts
      hfinTerminals hcertEta
  cases hrule : selectedRule P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      c.deltaShort c.deltaTerm c.l0 H S with
  | t1 =>
      rw [hrule] at hguard
      simp [selectorStep, hrule] at hout
      subst S'
      have hf := hfresh hguard
      apply hadvance (S.cursor + c.h) (by
        rw [hf.2.2.1]
        omega) (by simpa only [selectorStep, hrule] using hreadBound)
      exact ⟨rfl, by simp only [advanceCursor]; rw [hf.2.2.1], rfl⟩
  | t2 =>
      rw [hrule] at hguard
      simp [selectorStep, hrule] at hout
      subst S'
      have hs' := hsearch hguard.1
      apply hadvance (S.cursor + c.h) (by omega)
        (by simpa only [selectorStep, hrule] using hreadBound)
      exact ⟨rfl, by simpa only [advanceCursor] using hs'.2.1.trans (by omega), rfl⟩
  | t3 =>
      rw [hrule] at hguard
      simp [selectorStep, hrule] at hout
      subst S'
      have hs' := hsearch hguard.1
      apply hadvance (S.cursor + c.h) (by omega)
        (by simpa only [selectorStep, hrule] using hreadBound)
      exact ⟨rfl, by simpa only [advanceCursor] using hs'.2.1.trans (by omega), rfl⟩
  | t4 =>
      rw [hrule] at hguard
      simp [selectorStep, hrule] at hout
      subst S'
      have hs' := hsearch hguard.1
      apply hadvance (S.cursor + 2 * (c.l0 : ℤ))
        (by omega) (by simpa only [selectorStep, hrule] using hreadBound)
      exact ⟨rfl, by simpa only [advanceCursor] using hs'.2.1.trans (by omega), rfl⟩
  | t5 =>
      rw [hrule] at hguard
      have hs' := hsearch hguard.1
      have hread' := hread hrule
      have hcont' := hcont hrule
      have htQuery : S.cursor + 2 * (c.l0 : ℤ) ≤ Tquery := by
        simpa only [selectorStep, hrule] using hreadBound
      obtain ⟨-, hmu', hmean', hhistory', hdrift', hjump, hratio, hlo, hhi, -⟩ :=
        branchT5Data_of_alignedConstant hd hg hCd hstat hunit hdag hwin hY
          hbridge z hexact hs' hguard hout hread' cert hmu (by rw [hs]; exact hbaseCursor)
          hentry hcont'
      simp [selectorStep, hrule] at hout
      subst S'
      have hexact' : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar
          (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            jStar c.chop c.l0 S) := by
        simp only [ExactStateData, hopState, true_and]
        exact ⟨by omega, le_rfl⟩
      have hFpos : Book.Ch02.BlockPosDef
          (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ))) :=
        hread'.positiveMean _ (by omega) le_rfl
      have hmuOld : S.mu.PosDef := by rw [← hmu]; exact cert.mus_pos S.stage le_rfl
      have htarget : (canonicalMetric
          (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ)))).PosDef :=
        ShortHop.posDef_canonicalMetric (posDef_toFullBlockMat
          (Recurrence.isSymmetricBlockMat_adaptedMean P S.q _) hFpos)
      have hphase' : FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar
            (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
              jStar c.chop c.l0 S) ∨
          SearchInvariant c.h (hopState P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) jStar c.chop c.l0 S) ∨
          TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew c.etaX jStar
              (hopState P (initExpQ d g : ℝ) (initExpA g)
                (initExpRhoMax d g) jStar c.chop c.l0 S) ∧
            ∀ E0 : BlockMat d,
              (hopState P (initExpQ d g : ℝ) (initExpA g)
                (initExpRhoMax d g) jStar c.chop c.l0 S).candidate = some E0 →
              IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0 := by
        by_cases hfinal : projDist S.mu (canonicalMetric
          (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ)))) ≤ c.chop
        · right; right
          refine ⟨?_, ?_⟩
          · refine ⟨by simp [hopState, hfinal], rfl, rfl, hhistory', hdrift', ?_⟩
            refine ⟨adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ)),
              by simp [hopState, hfinal], ?_, ?_, ?_⟩
            · simpa [hopState, hfinal] using
                projPathStep_eq_target hmuOld htarget hfinal
            · simpa [hopState, hfinal] using hlo
            · simpa [hopState, hfinal] using hhi
          · intro E0 hE0
            simp [hopState, hfinal] at hE0
            subst E0
            exact ⟨Recurrence.isSymmetricBlockMat_adaptedMean P S.q _, hFpos⟩
        · left
          exact ⟨by simp [hopState, hfinal], rfl, rfl,
            by simp [hopState, hfinal], hhistory', hdrift'⟩
      have hfinTerminal : HasFiniteAdaptedMean P (cert.grids S.stage)
          (S.cursor + 2 * (c.l0 : ℤ)) := by
        rw [hq]
        exact hread'.finiteMean _ (by omega) le_rfl
      obtain ⟨cert', hmuNew, hqNew, hsNew, htNew, hetaNew, hcompleted,
          hkeep, hkeepOld, hstartsNew, hterminalsNew, hfinStartsNew,
          hfinTerminalsNew, hcertEtaNew, hstartsZeroNew⟩ :=
        cert.extend_finite hstartsZero
        (mu' := (hopState P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar c.chop c.l0 S).mu)
        (q' := (hopState P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar c.chop c.l0 S).q)
        (s' := S.cursor + (c.l0 : ℤ))
        (t := S.cursor + 2 * (c.l0 : ℤ))
        hmu' (by simp [hopState]) (by rw [hs]; omega)
        (by rw [hmu]; simpa [hopState] using hjump)
        (by rw [hq]; simpa [hopState] using hratio)
        c.etaX_pos.le c.etaX_le_quarter le_rfl hcertEta (by rw [hs]; omega) hstartsBound
        hterminalsBound (by omega) htQuery hfinStarts hfinTerminals
        (by simpa [hopState] using hnewFinite) hfinTerminal
      refine ⟨hexact', rfl, by simp [hopState]; omega, hhistory', hphase', cert',
        hmuNew, hqNew, hsNew, ?_,
        ?_, hstartsNew, hterminalsNew, hfinStartsNew, hfinTerminalsNew,
        hcertEtaNew, ?_⟩
      · change S.prefixLoss + detLoss P S.q S.cursor
            (S.cursor + 2 * (c.l0 : ℤ)) = cert'.completedLoss +
          detLoss P (roundedGrid jStar (projPathStep c.chop S.mu
            (canonicalMetric (adaptedMean P S.q
              (S.cursor + 2 * (c.l0 : ℤ))))))
            (S.cursor + (c.l0 : ℤ)) (S.cursor + (c.l0 : ℤ))
        rw [detLoss_self, add_zero, hcompleted, hq, hs, hloss]
        calc
          cert.completedLoss + detLoss P S.q S.base S.cursor +
              detLoss P S.q S.cursor (S.cursor + 2 * (c.l0 : ℤ)) =
            cert.completedLoss + (detLoss P S.q S.base S.cursor +
              detLoss P S.q S.cursor (S.cursor + 2 * (c.l0 : ℤ))) := by ring
          _ = _ := by rw [detLoss_add]
      · intro i hi
        by_cases hik : i = S.stage
        · subst i
          rcases hkeep S.stage le_rfl with ⟨-, hgridOld, -⟩
          rw [hgridOld, hq, htNew, hetaNew, hqNew, hsNew]
          exact ⟨hlo, hhi⟩
        · have hiold : i < S.stage := by simp [hopState] at hi; omega
          rcases hkeep i hiold.le with ⟨-, hgridOld, -⟩
          rcases hkeep (i + 1) (by omega) with ⟨-, hgridNext, hstartNext⟩
          rcases hkeepOld i hiold with ⟨hterminalOld, hetaOld⟩
          rw [hgridOld, hgridNext, hstartNext, hterminalOld, hetaOld]
          exact hcertBridge i hiold
      · exact hstartsZeroNew
  | t6 =>
      rw [hrule] at hguard
      simp [selectorStep, hrule] at hout
      subst S'
      have ht := hterminal hguard.1
      apply hadvance (S.base + max (H : ℤ) c.h)
        (by rw [← hbaseCheckpoint]; have := le_max_right (H : ℤ) c.h; omega)
        (by simpa only [selectorStep, hrule] using hreadBound)
      exact ⟨rfl, by simp [advanceCursor]; rw [← ht.2.1]; omega,
        rfl⟩
  | t7 => simp [selectorStep, hrule] at hout

end

end Homogenization.HighContrast.Selection
