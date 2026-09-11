/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.RunInvariantHop

/-!
# Definedness along the projective-hop prefix

The proof-only hop certificate retains finite adapted means at every recorded
start and completed terminal.  These conclusions are derived while the actual
selector trace is traversed; they are not fields of the executable state.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Appending an actual hop preserves finite means at all earlier certificate
scales and records finite means at its new start and terminal. -/
theorem HopPrefixCertificate.extend_finite
    {P : Measure (CoeffSpace d)} {jStar : ℤ} {chop Khop : ℝ}
    {l0 : ℕ} {r0 Tquery : ℤ} {k : ℕ}
    (cert : HopPrefixCertificate P jStar chop Khop l0 r0 k)
    (hstartsZero : cert.starts 0 = r0)
    {mu' q' : Mat d} {s' t : ℤ} {eta' etaMax : ℝ}
    (hmu' : mu'.PosDef) (hq' : q' = roundedGrid jStar mu')
    (hscale : cert.starts k + (l0 : ℤ) ≤ s')
    (hhop : projDist (cert.mus k) mu' ≤ chop)
    (hgrid : gridRatio (cert.grids k) q' ≤ Khop)
    (heta0 : 0 ≤ eta') (heta4 : eta' ≤ 1 / 4)
    (hetaMax : eta' ≤ etaMax)
    (hcertEta : ∀ i : ℕ, i < k → cert.eta i ≤ etaMax)
    (hterminal : cert.starts k ≤ t)
    (hstartsBound : ∀ i : ℕ, i ≤ k → cert.starts i ≤ Tquery)
    (hterminalsBound : ∀ i : ℕ, i < k → cert.terminals i ≤ Tquery)
    (hs'Bound : s' ≤ Tquery) (htBound : t ≤ Tquery)
    (hfinStarts : ∀ i : ℕ, i ≤ k →
      HasFiniteAdaptedMean P (cert.grids i) (cert.starts i))
    (hfinTerminals : ∀ i : ℕ, i < k →
      HasFiniteAdaptedMean P (cert.grids i) (cert.terminals i))
    (hfinStart' : HasFiniteAdaptedMean P q' s')
    (hfinTerminal : HasFiniteAdaptedMean P (cert.grids k) t) :
    ∃ cert' : HopPrefixCertificate P jStar chop Khop l0 r0 (k + 1),
      cert'.mus (k + 1) = mu' ∧ cert'.grids (k + 1) = q' ∧
        cert'.starts (k + 1) = s' ∧ cert'.terminals k = t ∧
        cert'.eta k = eta' ∧
        cert'.completedLoss = cert.completedLoss +
          detLoss P (cert.grids k) (cert.starts k) t ∧
        (∀ i : ℕ, i ≤ k → cert'.mus i = cert.mus i ∧
          cert'.grids i = cert.grids i ∧ cert'.starts i = cert.starts i) ∧
        (∀ i : ℕ, i < k →
          cert'.terminals i = cert.terminals i ∧ cert'.eta i = cert.eta i) ∧
        (∀ i : ℕ, i ≤ k + 1 → cert'.starts i ≤ Tquery) ∧
        (∀ i : ℕ, i < k + 1 → cert'.terminals i ≤ Tquery) ∧
        (∀ i : ℕ, i ≤ k + 1 →
          HasFiniteAdaptedMean P (cert'.grids i) (cert'.starts i)) ∧
        (∀ i : ℕ, i < k + 1 →
          HasFiniteAdaptedMean P (cert'.grids i) (cert'.terminals i)) ∧
        (∀ i : ℕ, i < k + 1 → cert'.eta i ≤ etaMax) ∧
        cert'.starts 0 = r0 := by
  obtain ⟨cert', hmuNew, hqNew, hsNew, htNew, hetaNew, hcompleted,
      hkeep, hkeepOld, hstartsNew, hterminalsNew⟩ := cert.extend hmu' hq' hscale
    hhop hgrid heta0 heta4 hterminal hstartsBound hterminalsBound hs'Bound htBound
  refine ⟨cert', hmuNew, hqNew, hsNew, htNew, hetaNew, hcompleted, hkeep,
    hkeepOld, hstartsNew, hterminalsNew, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hik : i = k + 1
    · subst i
      rwa [hqNew, hsNew]
    · rcases hkeep i (by omega) with ⟨-, hgridOld, hstartOld⟩
      rw [hgridOld, hstartOld]
      exact hfinStarts i (by omega)
  · intro i hi
    by_cases hik : i = k
    · subst i
      rcases hkeep k le_rfl with ⟨-, hgridOld, -⟩
      rwa [hgridOld, htNew]
    · rcases hkeep i (by omega) with ⟨-, hgridOld, -⟩
      rcases hkeepOld i (by omega) with ⟨hterminalOld, -⟩
      rw [hgridOld, hterminalOld]
      exact hfinTerminals i (by omega)
  · intro i hi
    by_cases hik : i = k
    · subst i
      rwa [hetaNew]
    · rw [(hkeepOld i (by omega)).2]
      exact hcertEta i (by omega)
  · exact (hkeep 0 (Nat.zero_le k)).2.2.trans hstartsZero

/-- A same-grid cursor advance preserves every recorded finite-mean fact. -/
theorem HopPrefixCertificate.advanceCursor_finite
    {P : Measure (CoeffSpace d)} {jStar : ℤ} {chop Khop : ℝ}
    {l0 : ℕ} {r0 Tquery : ℤ} {etaMax : ℝ} {S : State d}
    (cert : HopPrefixCertificate P jStar chop Khop l0 r0 S.stage)
    (hstartsZero : cert.starts 0 = r0)
    (hmu : cert.mus S.stage = S.mu) (hq : cert.grids S.stage = S.q)
    (hs : cert.starts S.stage = S.base)
    (hloss : S.prefixLoss = cert.completedLoss +
      detLoss P S.q S.base S.cursor)
    (hbridge : ∀ i : ℕ, i < S.stage →
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
    (hcertEta : ∀ i : ℕ, i < S.stage → cert.eta i ≤ etaMax)
    (v : ℤ) :
    ∃ cert' : HopPrefixCertificate P jStar chop Khop l0 r0
        (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage,
      cert'.mus (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage =
          (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).mu ∧
        cert'.grids (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage =
          (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).q ∧
        cert'.starts (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage =
          (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).base ∧
        (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).prefixLoss =
          cert'.completedLoss +
          detLoss P (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).q
            (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).base
            (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).cursor ∧
        (∀ i : ℕ,
          i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
          BlockMatLoewnerLE (blockScale (1 - cert'.eta i)
            (adaptedMean P (cert'.grids i) (cert'.terminals i)))
            (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1))) ∧
          BlockMatLoewnerLE
            (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1)))
            (blockScale (1 + cert'.eta i)
              (adaptedMean P (cert'.grids i) (cert'.terminals i)))) ∧
        (∀ i : ℕ,
          i ≤ (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
          cert'.starts i ≤ Tquery) ∧
        (∀ i : ℕ,
          i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
          cert'.terminals i ≤ Tquery) ∧
        (∀ i : ℕ,
          i ≤ (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
          HasFiniteAdaptedMean P (cert'.grids i) (cert'.starts i)) ∧
        (∀ i : ℕ,
          i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
          HasFiniteAdaptedMean P (cert'.grids i) (cert'.terminals i)) ∧
        (∀ i : ℕ,
          i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
            cert'.eta i ≤ etaMax) ∧
        cert'.starts 0 = r0 := by
  refine ⟨cert, ?_⟩
  change cert.mus S.stage = S.mu ∧ cert.grids S.stage = S.q ∧
    cert.starts S.stage = S.base ∧
      S.prefixLoss + detLoss P S.q S.cursor v = cert.completedLoss +
        detLoss P S.q S.base v ∧
      (∀ i : ℕ, i < S.stage →
        BlockMatLoewnerLE (blockScale (1 - cert.eta i)
          (adaptedMean P (cert.grids i) (cert.terminals i)))
          (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1))) ∧
        BlockMatLoewnerLE
          (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1)))
          (blockScale (1 + cert.eta i)
            (adaptedMean P (cert.grids i) (cert.terminals i)))) ∧
      (∀ i : ℕ, i ≤ S.stage → cert.starts i ≤ Tquery) ∧
      (∀ i : ℕ, i < S.stage → cert.terminals i ≤ Tquery) ∧
      (∀ i : ℕ, i ≤ S.stage →
        HasFiniteAdaptedMean P (cert.grids i) (cert.starts i)) ∧
      (∀ i : ℕ, i < S.stage →
        HasFiniteAdaptedMean P (cert.grids i) (cert.terminals i)) ∧
      (∀ i : ℕ, i < S.stage → cert.eta i ≤ etaMax) ∧
      cert.starts 0 = r0
  refine ⟨hmu, hq, hs, ?_, hbridge, hstartsBound, hterminalsBound,
    hfinStarts, hfinTerminals, hcertEta, hstartsZero⟩
  rw [hloss]
  calc
    cert.completedLoss + detLoss P S.q S.base S.cursor +
        detLoss P S.q S.cursor v =
      cert.completedLoss + (detLoss P S.q S.base S.cursor +
        detLoss P S.q S.cursor v) := by ring
    _ = cert.completedLoss + detLoss P S.q S.base v := by rw [detLoss_add]

variable {H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- A genuine same-grid cursor step preserves the complete run invariant,
including the proof-side finite-mean facts. -/
theorem advanceCursor_next_invariants
    {P : Measure (CoeffSpace d)} {jStar r0 Tquery v : ℤ} {S : State d}
    (hv : S.checkpoint ≤ v) (hvQuery : v ≤ Tquery)
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hbaseCheckpoint : S.base = S.checkpoint)
    (hhistory : stateHistory S ≤ ENNReal.ofReal c.etaIn)
    (hsearch : SearchInvariant c.h
      (Homogenization.HighContrast.Selection.advanceCursor P S v .search none))
    (cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 S.stage)
    (hstartsZero : cert.starts 0 = r0)
    (hmu : cert.mus S.stage = S.mu) (hq : cert.grids S.stage = S.q)
    (hs : cert.starts S.stage = S.base)
    (hloss : S.prefixLoss = cert.completedLoss + detLoss P S.q S.base S.cursor)
    (hbridge : ∀ i : ℕ, i < S.stage →
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
    ExactStateData P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        jStar (Homogenization.HighContrast.Selection.advanceCursor P S v .search none) ∧
      (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).base =
        (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).checkpoint ∧
      (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).cursor ≤
        Tquery ∧
      stateHistory (Homogenization.HighContrast.Selection.advanceCursor P S v .search none) ≤
        ENNReal.ofReal c.etaIn ∧
      (FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar
          (Homogenization.HighContrast.Selection.advanceCursor P S v .search none) ∨
        SearchInvariant c.h
          (Homogenization.HighContrast.Selection.advanceCursor P S v .search none) ∨
        TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew c.etaX jStar
            (Homogenization.HighContrast.Selection.advanceCursor P S v .search none) ∧
          ∀ E0 : BlockMat d,
            (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).candidate =
              some E0 → IsSymmetricBlockMat E0 ∧ Book.Ch02.BlockPosDef E0) ∧
      ∃ cert' : HopPrefixCertificate P jStar c.chop Khop c.l0 r0
          (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage,
        cert'.mus (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage =
            (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).mu ∧
          cert'.grids
              (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage =
            (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).q ∧
          cert'.starts
              (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage =
            (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).base ∧
          (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).prefixLoss =
            cert'.completedLoss + detLoss P
              (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).q
              (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).base
              (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).cursor ∧
          (∀ i : ℕ,
            i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
              BlockMatLoewnerLE (blockScale (1 - cert'.eta i)
                (adaptedMean P (cert'.grids i) (cert'.terminals i)))
                (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1))) ∧
              BlockMatLoewnerLE
                (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1)))
                (blockScale (1 + cert'.eta i)
                  (adaptedMean P (cert'.grids i) (cert'.terminals i)))) ∧
          (∀ i : ℕ,
            i ≤ (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
              cert'.starts i ≤ Tquery) ∧
          (∀ i : ℕ,
            i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
              cert'.terminals i ≤ Tquery) ∧
          (∀ i : ℕ,
            i ≤ (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
              HasFiniteAdaptedMean P (cert'.grids i) (cert'.starts i)) ∧
          (∀ i : ℕ,
            i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
              HasFiniteAdaptedMean P (cert'.grids i) (cert'.terminals i)) ∧
          (∀ i : ℕ,
            i < (Homogenization.HighContrast.Selection.advanceCursor P S v .search none).stage →
              cert'.eta i ≤ c.etaX) ∧
          cert'.starts 0 = r0 := by
  refine ⟨exactStateData_advanceCursor hexact hv, hbaseCheckpoint, hvQuery, ?_,
    Or.inr (Or.inl hsearch), ?_⟩
  · simpa only [stateHistory, Homogenization.HighContrast.Selection.advanceCursor] using
      hhistory
  · exact cert.advanceCursor_finite hstartsZero hmu hq hs hloss hbridge hstartsBound
      hterminalsBound hfinStarts hfinTerminals hcertEta v

end

end Homogenization.HighContrast.Selection
