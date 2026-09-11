/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Provider.Bridge.BridgeAssembly

/-!
# Proposition `p.successful.short.bridge`

The two-grid means and the shifted determinant drift.  Between two rounded grids
of the same alignment, at a scale separation large enough for the cross-grid
factor, the annealed block of the new grid at a scale is squeezed between the
old grid's blocks one separation below and one separation above, with errors
built from the separation, the old grid's weighted determinant drift, and one
displayed source remainder; and if the lower squeeze holds with a small enough
slack, the new grid's own weighted drift is controlled by that slack, the
separation, the old grid's drift shifted by the separation, and a second source
remainder.

Both errors and both remainders are the printed ones, written out in the carrier
layer, so the statement displays exactly where the two absolute grid
eccentricities and the reference contrast are paid: inside the bridge source
coefficient, and nowhere else.  The base constant is a function of the dimension
and the growth exponent alone, and that is carried by the binder order — it is
bound before the dimensional constant of the source-control subsection, before
the law, before the reference block, and before both witnesses and every scale.

Those two constants play different roles and neither dominates the other.  The
dimensional constant names one thing only: the coefficient of the pathwise cell
bounds that the window multiplier carries, and through it the boundary constant
inside the bridge source coefficient.  The counting constant of the cross-grid
boundary row — which the reference text writes with the same symbol — is not a
parameter here at all; it is a deterministic geometric fact of the two grids,
proved with its own dimensional constant, and the base constant absorbs it.
That is what lets the base constant be chosen before the dimensional constant,
and it is what the composition with the short test needs, since the short test
binds the base constant ahead of its own dimensional constant.

The exponents are the fixed ones of the bridge subsection, not free parameters.
This statement reads two of them — the moment exponent, at which the coupled
window is read, and the drift weight, which weights the determinant drift.  It
reads neither the maximal weight nor the history exponent.

There is no extended-real quantity anywhere in this statement.  Every displayed
inequality is between real numbers or in the doubled Loewner order, so none of
the fixed-grid layer's clamping conventions is in play, and no supremum,
integral or moment is named.

The printed hypothesis "every cell read below — target, packed, selected,
triangulated, and terminal, in both grid orientations — lies in the window" is
carried by the containment of the two grid towers over the scales the estimates
read, exactly as in the transport.  The five families reduce for three reasons.
The target cells and the terminal cells are tower members outright.  The packed
cells, the selected cells of the maximal filling — including those at scales
below the burn, which lie outside the tower range and are reached only through
the target cell that contains them — and the residual triangulation are all
contained in a target cell by construction, hence in a tower cell by
transitivity.  The aligned subcells of a tower cell are contained in it because
the ratio of the two side lengths is an odd power of three, the mechanism the
transport records.

Definedness is neither assumed nor concluded.  The tower containment, the window
multiplier and the terminal block of `e.source.adapted.bound` force the
annealed blocks of both grids to be finite and positive definite on the towers,
which is what makes the weighted drift read a genuine inverse; the statement
therefore names no finiteness hypothesis, as the reference text does not.  The
cross-grid comparison that chain needs is available for free here, because this
statement does not fix the rounded-hop constant: any bound above the three
relevant cross-grid factors serves, and the cross-grid factor is at least one.
-/

theorem HCPoly.Frozen.random_source_bridge_two_grid_shifted_drift
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Cd : ℝ, 1 ≤ Cd →
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
        (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ,
          Homogenization.HighContrast.IsCoupledWindow d
            (Homogenization.HighContrast.initExpQ d g : ℝ) K jStar M →
          ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
            Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M
              Y →
                    (∀ mp mv : Homogenization.Mat d, mp.PosDef → mv.PosDef →
                      ∀ nn l : ℤ, jStar ≤ nn - l →
                        C *
                            (1 +
                              Real.log
                                (Homogenization.HighContrast.gridRatio
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (Homogenization.HighContrast.roundedGrid jStar
                                    mv))) ≤ (l : ℝ) →
                        C *
                              Homogenization.HighContrast.gridRatio
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (Homogenization.HighContrast.roundedGrid jStar mv) *
                              (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
                        (∀ r : Homogenization.Mat d,
                          r = Homogenization.HighContrast.roundedGrid jStar mp ∨
                            r = Homogenization.HighContrast.roundedGrid jStar mv →
                          ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
                            Homogenization.HighContrast.adaptedCell r j ⊆
                              Homogenization.HighContrast.centeredCube d M) →
                        Homogenization.BlockMatLoewnerLE
                            (Homogenization.HighContrast.blockSub
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                nn)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (nn - l)))
                            (Homogenization.HighContrast.blockScale
                              (Homogenization.HighContrast.bridgeErrUpper C Cd g
                                (Homogenization.HighContrast.initExpRhoDr g)
                                (Homogenization.HighContrast.gridRatio
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (Homogenization.HighContrast.roundedGrid jStar mv))
                                P E jStar mp mv nn l)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                nn)) ∧
                          Homogenization.BlockMatLoewnerLE
                            (Homogenization.HighContrast.blockScale
                              (-Homogenization.HighContrast.bridgeErrLower C Cd g
                                (Homogenization.HighContrast.initExpRhoDr g)
                                (Homogenization.HighContrast.gridRatio
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (Homogenization.HighContrast.roundedGrid jStar mv))
                                P E jStar mp mv nn l)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (nn + l)))
                            (Homogenization.HighContrast.blockSub
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                nn)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (nn + l))) ∧
                          ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
                            Homogenization.BlockMatLoewnerLE
                              (Homogenization.HighContrast.blockScale (1 - eta)
                                (Homogenization.HighContrast.adaptedMean P
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (nn + l)))
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                nn) →
                            Homogenization.HighContrast.linearDrift P
                                (Homogenization.HighContrast.initExpRhoDr g)
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                jStar nn ≤
                              C *
                                (eta +
                                  Homogenization.HighContrast.gridRatio
                                      (Homogenization.HighContrast.roundedGrid jStar
                                        mp)
                                      (Homogenization.HighContrast.roundedGrid jStar
                                        mv) *
                                    (3 : ℝ) ^ (-(l : ℝ)) +
                                  (1 +
                                      Homogenization.HighContrast.gridRatio
                                        (Homogenization.HighContrast.roundedGrid
                                          jStar mp)
                                        (Homogenization.HighContrast.roundedGrid
                                          jStar mv)) *
                                    (3 : ℝ) ^
                                      (2 *
                                        Homogenization.HighContrast.initExpRhoDr g *
                                        (l : ℝ)) *
                                    Homogenization.HighContrast.linearDrift P
                                      (Homogenization.HighContrast.initExpRhoDr g)
                                      (Homogenization.HighContrast.roundedGrid jStar
                                        mp)
                                      jStar (nn + l) +
                                  Homogenization.HighContrast.bridgeShiftedRemainder
                                    C Cd g
                                    (Homogenization.HighContrast.initExpRhoDr g) E
                                    jStar mp mv nn l))
    := by
  exact
    Homogenization.HighContrast.Bridge.random_source_bridge_two_grid_shifted_drift_assembly
      d hd g hg
