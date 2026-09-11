/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SelectionObjects
import HCPoly.Provider.Selection.RandomSourceGlobalSelectionAssembly
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger

/-!
# Proposition `p.global.selection`

One-pass global selection with a random source.  Every structural constant of
the selection is fixed before the coefficient law, its source scale, its gauge,
its reference block and its aspect ratio; the law then determines one adapted
grid, one base block, and one terminal window, on which the complete
non-restarted histories are small, the two endpoints are determinant- and
drift-calm, and the whole windowed source account is available at a single
bounded window read by a single multiplier.

The constants are produced in the printed order, and the order is what the
statement exports.  The witness radius and grid exponents, the three profile
tolerances, the terminal determinant tolerance and the portable constant are
fixed first and do not depend on the lower scale buffer; only the buffer itself
and the two length coefficients do, so those are produced after a prescribed
lower bound for the buffer is given.  A consumer that must fix its own response
data against the radius exponent, and only then prescribe the buffer, reads
exactly this order.

The alignment is the coupled execution burn, and the window is the cube whose
height above the burn is the ceiling of the execution coefficient against
`log_3(2 + Π)`.  Both are determined by the law's data and the constants already
fixed; the statement therefore names them by their defining equations rather
than existentially, and it concludes that the pair is a coupled window pair, so
that the multiplier of the window lemma is available at exactly this pair, that
the window has positive height, and that the burn obeys the additive bound the
entry argument pays once.

The multiplier is data, as in the neighbouring source results: the printed
statement constructs it from the window lemma at the pair the selection has just
fixed, and the corresponding hypothesis is that lemma's conclusion, carried by
`IsWindowMultiplier`.  It is bound after the returned tuple and reaches only the
source account, which is how the printed determinism requirement is carried: the
selected grid, base block and scales are determined by the law alone, and no
state component is conditioned on any realization of the multiplier.

The dimensional constant of the source-control subsection is a parameter, not a
witness, and it is bound before every constant this statement produces: the
source account below is read at that constant, and the constants produced here
may absorb it.

The returned tuple is the printed one.  Its base block and its actual witness
are the canonical metric of that block; its rounded grid is that metric rounded
at the burn; its two scales are separated by exactly the prescribed terminal
length; and the four scale bounds, the enclosure of every cell the selection
reads, the base-block calibration, the two determinant and drift bounds, the
history bounds, and the whole source collection are its properties.

The reference text also records the finite-prefix bookkeeping that produces the
tuple: the state, its potential, the ordered transitions, the per-step potential
drop, the determinant charges, and the transition count.  Those quantities are
internal to the construction — the transition system itself is defined only
inside the argument — and no result of the development reads them.  They are not
part of this statement.

Well-definedness is neither assumed nor concluded here.  The window, its
multiplier and the enclosure force the annealed blocks of the grid to be finite
and positive definite at every scale of the terminal range, and the consumer
derives them there, from the aligned partition of the terminal cell and integer
stationarity; the histories, the profile and the determinant roots below denote
the printed quantities on exactly that account.
-/

theorem HCPoly.Frozen.random_source_global_selection
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
  exact Homogenization.HighContrast.Selection.random_source_global_selection_assembly
    d hd g hg cStar hcStar epsCal hepsCalLo hepsCalHi etaDr hetaDrLo hetaDrHi
    etaProfBar hetaProfLo hetaProfHi deltaDetBar hdeltaDetLo hdeltaDetHi H hH
