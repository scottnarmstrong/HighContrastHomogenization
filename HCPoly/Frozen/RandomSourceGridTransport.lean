/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Provider.Transport.RandomSourceGridTransportAssembly

/-!
# Proposition `p.two.grid.transport`

Transport of complete histories across one change of adapted geometry.  A
bounded projective step between two rounded grids of the same alignment carries
the whole fluctuation history from the old grid to the new one: the exact pair
of histories on the new grid at the new terminal scale is majorized by the
incoming portable profile of the old grid at its terminal scale, plus the bridge
error, plus one displayed source majorant.

The source is paid only through the bounded-window control of
`e.source.adapted.bound`, whose multiplier is the datum bound before every
grid, scale and cell.  The absolute eccentricities of the two witnesses are
paid only inside the displayed source coefficients: the base constant is
independent of the reference contrast, of the aspect ratio, of the law, and of
both eccentricities, and that independence is carried by the binder order —
the buffer threshold and the base constant are bound before the law, the
reference block, and the two witnesses.

The exponents are the ones the subsection fixes: an even moment exponent at
least two, a maximal weight strictly between the growth exponent and one, and
the derived history exponent, subject to the two printed admissibility
conditions.  The derived exponent is weaker than the fixed-grid admissibility
of `p.fixed.geometry.one.grid.propagation`, so a consumer feeds the transported history
straight into that proposition.

Well-definedness is a conclusion, not a hypothesis.  Under the containment of
the two grid towers in the window the annealed blocks of both grids are finite
and positive definite at every scale of the range, their centered moments are
finite, and the means are ordered; the histories and the profile therefore
denote the printed quantities.

The containment hypothesis is exactly the two grid towers, and it is worth
saying why, because the reference text's own list is longer.  That list also
names the two terminal cells, the cells selected below the burn, and the target,
centered, early and Whitney cells.  The two terminal cells are members of the
towers.  The remaining families reduce for three separate reasons, and only the
first is arithmetic.

A target cell, and likewise a cell of either centered history, is an aligned
cell of some scale inside a cell of a larger scale on the same grid.  Such a
cell is *contained* in the larger one, not merely centered in it, and this is a
property of the triadic ratio rather than a general fact about cubes: the cells
are open, the aligned centers are integer multiples of the smaller side length,
and the ratio of the two side lengths is an odd power of three.  An integer
offset whose center lies in the larger open cube is therefore at most half of
that odd number minus one half, and adding the smaller half-width returns
exactly the larger half-width.  The containment is an equality at the extreme
offset, and it would fail for an even ratio.

The filling, Whitney and below-burn cells need no arithmetic: the maximal
filling of a target cell selects only cells contained in that cell, and a
Whitney row is a filling of a cell already selected, so every one of them lies
inside the target cell it came from, hence inside a terminal cell.

The scale-`b` ancestors of the inherited rows are not a containment obligation
at all.  They enter only as the index set of a stationarity comparison — the
supremum attached to an ancestor is dominated in distribution by the centered
history at the checkpoint — and a comparison in law reads no cell of the window.
-/

theorem HCPoly.Frozen.random_source_grid_transport
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Q : ℕ) (hQ : 2 ≤ Q) (hQeven : Even Q)
    (rhoMax : ℝ) (hrhoLo : g < rhoMax) (hrhoHi : rhoMax < 1)
    (a : ℝ) (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (halo : 0 < a) (hahi : a < 1 - g)
    (hasum : 0 < ((d : ℝ) + 1) / 2 - g - a / (Q : ℝ))
    (Khop : ℝ) (hKhop : 1 ≤ Khop) :
    ∃ Ltr : ℕ, 1 ≤ Ltr ∧
      ∃ Ctr : ℝ, 0 < Ctr ∧
        ∀ l0 : ℕ, Ltr ≤ l0 →
        ∀ Cd : ℝ, 1 ≤ Cd →
        ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
          (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
          MeasureTheory.IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
          HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
          ∀ jStar M : ℤ,
            Homogenization.HighContrast.IsCoupledWindow d Q K jStar M →
            ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
              Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M
                Y →
              ∀ mu mu' : Homogenization.Mat d, mu.PosDef → mu'.PosDef →
                Homogenization.HighContrast.gridRatio
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (Homogenization.HighContrast.roundedGrid jStar mu') ≤ Khop →
                ∀ rchk u : ℤ, jStar ≤ rchk → rchk ≤ u →
                  -- every cell read lies in the window
                  (∀ r : Homogenization.Mat d,
                    r = Homogenization.HighContrast.roundedGrid jStar mu ∨
                      r = Homogenization.HighContrast.roundedGrid jStar mu' →
                    ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
                      Homogenization.HighContrast.adaptedCell r j ⊆
                        Homogenization.HighContrast.centeredCube d M) →
        -- the annealed blocks of both grids are finite, positive definite,
        -- have finite centered moments, and are ordered
        ((∀ r : Homogenization.Mat d,
            r = Homogenization.HighContrast.roundedGrid jStar mu ∨
              r = Homogenization.HighContrast.roundedGrid jStar mu' →
            ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
              Homogenization.HighContrast.HasFiniteAdaptedMean P r j ∧
                Homogenization.Book.Ch02.BlockPosDef
                  (Homogenization.HighContrast.adaptedMean P r j) ∧
                Homogenization.HighContrast.centeredMoment P (Q : ℝ) r j ≠ ⊤) ∧
          (∀ r : Homogenization.Mat d,
            r = Homogenization.HighContrast.roundedGrid jStar mu ∨
              r = Homogenization.HighContrast.roundedGrid jStar mu' →
            ∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ u + 2 * (l0 : ℤ) →
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.adaptedMean P r T)
                (Homogenization.HighContrast.adaptedMean P r j)) ∧
          -- the transported history, the bridge normalization, the bridge
          -- determinant
          ∀ etaX : ℝ, 0 ≤ etaX → etaX ≤ 1 / 4 →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.blockScale (1 - etaX)
                (Homogenization.HighContrast.adaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mu)
                  (u + 2 * (l0 : ℤ))))
              (Homogenization.HighContrast.adaptedMean P
                (Homogenization.HighContrast.roundedGrid jStar mu')
                (u + (l0 : ℤ))) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.adaptedMean P
                (Homogenization.HighContrast.roundedGrid jStar mu')
                (u + (l0 : ℤ)))
              (Homogenization.HighContrast.blockScale (1 + etaX)
                (Homogenization.HighContrast.adaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mu)
                  (u + 2 * (l0 : ℤ)))) →
            (Homogenization.HighContrast.centeredHistory P (Q : ℝ) rhoMax
                  (Homogenization.HighContrast.roundedGrid jStar mu') jStar
                  (u + (l0 : ℤ)) +
                Homogenization.HighContrast.nonlinearHistory P (Q : ℝ) a
                  (Homogenization.HighContrast.roundedGrid jStar mu') jStar
                  (u + (l0 : ℤ)) ≤
              ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
                  Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax
                    (Homogenization.HighContrast.roundedGrid jStar mu) jStar rchk
                    (u + 2 * (l0 : ℤ)) +
                ENNReal.ofReal (Ctr * etaX) +
                ENNReal.ofReal
                  (Ctr * (3 : ℝ) ^ (a * (l0 : ℝ)) *
                    Homogenization.HighContrast.transportSrcRemainder Cd g (Q : ℝ)
                      a E jStar mu mu' (u + (l0 : ℤ)))) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.blockScale (1 + etaX)⁻¹
                  (Homogenization.Book.Ch02.blockIdentity d))
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ)))) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ))))
                (Homogenization.HighContrast.blockScale (1 - etaX)⁻¹
                  (Homogenization.Book.Ch02.blockIdentity d)) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.blockScale
                  (1 - etaX / (1 - etaX))
                  (Homogenization.Book.Ch02.blockIdentity d))
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ)))) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ))))
                (Homogenization.HighContrast.blockScale
                  (1 + etaX / (1 - etaX))
                  (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (1 - etaX) ^ 2 *
                  Homogenization.HighContrast.adaptedDetRoot P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)) ≤
                Homogenization.HighContrast.adaptedDetRoot P
                  (Homogenization.HighContrast.roundedGrid jStar mu')
                  (u + (l0 : ℤ)) ∧
              Homogenization.HighContrast.adaptedDetRoot P
                  (Homogenization.HighContrast.roundedGrid jStar mu')
                  (u + (l0 : ℤ)) ≤
                (1 + etaX) ^ 2 *
                  Homogenization.HighContrast.adaptedDetRoot P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
    := by
  exact Homogenization.HighContrast.Transport.random_source_grid_transport_assembly
    d hd g hg Q hQ hQeven rhoMax hrhoLo hrhoHi a hadef halo hahi hasum
    Khop hKhop
