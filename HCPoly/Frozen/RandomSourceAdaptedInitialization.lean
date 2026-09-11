/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SourceObjects
import HCPoly.Provider.Initialization.InitializationAssembly

/-!
# Proposition `p.initial.fixed.grid.scale`

Bounded-window random-source initialization.  With the random-source data — unit
range of dependence is **not** assumed — a coupled window pair, and the common
multiplier of the window, every adapted cell of every deterministic rounded grid
at the burn alignment that lies inside the window has a finite positive definite
mean, a two-sided reference comparison, a bounded raw and centered `L^Q(S_Q)`
moment, a bounded mean transport, and a bounded determinant increment; on the
identity grid all four are bounded by the aspect ratio alone.

The exponent is the one fixed at `e.scale.selection.Q.choice`,
and only that one enters here.

The separation of the pathwise conclusion from the deterministic ones is part of
the statement.  The pathwise domination by the multiplier holds on one event of
full measure, simultaneously for every deterministic witness and every
admissible index; every other conclusion is an inequality between deterministic
matrices or numbers and carries no exceptional event, so it may be instantiated
at an index produced by a realization, and at a second window.

No deterministic pathwise lower bound is asserted: the pathwise upper bound
retains the unbounded multiplier, and inverting the adjoint row would give only
a bound whose right side is unbounded below.
The dimensional constant of the source-control subsection is a parameter, not a
witness of this statement: it is fixed once, sufficiently large for the filling
and Whitney estimates, and produced by `e.source.multiplier`, which is
also what supplies the multiplier bound this statement binds.  Both the
hypothesis that names it and every conclusion that names it are monotone in it,
so quantifying it universally above one is the faithful reading of a constant
fixed before the subsection's results.
-/

theorem HCPoly.Frozen.random_source_adapted_initialization
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ CdQ : ℝ, 0 < CdQ ∧
      ∀ Cd : ℝ, 1 ≤ Cd →
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
        (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ,
          Homogenization.HighContrast.IsCoupledWindow d
              ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ) K jStar M →
          ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
            Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M Y →
        -- the reference quantities
        (1 ≤ Homogenization.HighContrast.refContrast E ∧
            Homogenization.HighContrast.refContrast E ≤
              Homogenization.HighContrast.aspectRatio E ∧
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.blockSharp E) E ∧
            Homogenization.HighContrast.kappaRef E ≤
              1 + 6 * (Homogenization.HighContrast.refContrast E - 1) ∧
            1 + 6 * (Homogenization.HighContrast.refContrast E - 1) ≤
              6 * Homogenization.HighContrast.aspectRatio E) ∧
        -- the multiplier bound
        (ENNReal.ofReal (∫ a, Y a ∂P) ≤
            Homogenization.HighContrast.lqNorm P
              ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ) Y ∧
            Homogenization.HighContrast.lqNorm P
                ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ) Y ≤ 2) ∧
        -- the boundary constant is at least one
        (∀ mu : Homogenization.Mat d, mu.PosDef →
            1 ≤ Homogenization.HighContrast.boundaryConst Cd g mu) ∧
        -- the pathwise domination, on the single event of the window
        (∀ᵐ a ∂P, ∀ mu : Homogenization.Mat d, mu.PosDef →
            ∀ (r : ℤ) (w : Fin d → ℤ),
              Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M r w →
              Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedResponse
                    (Homogenization.HighContrast.roundedGrid jStar mu) r w a)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * Y a) E) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.coarseStarInv
                    (Homogenization.HighContrast.adaptedCellAt
                      (Homogenization.HighContrast.roundedGrid jStar mu) r w) a)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * Y a)
                    (Homogenization.blockReflect E))) ∧
        -- the deterministic cell conclusions
        (∀ mu : Homogenization.Mat d, mu.PosDef → ∀ (r : ℤ) (w : Fin d → ℤ),
            Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M r w →
              Homogenization.HighContrast.HasFiniteAdaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mu) r ∧
                Homogenization.Book.Ch02.BlockPosDef
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * 2)⁻¹
                    (Homogenization.HighContrast.blockSharp E))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * 2) E) ∧
                Homogenization.HighContrast.lqSchattenSize P
                    ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ)
                    (Homogenization.HighContrast.adaptedResponse
                      (Homogenization.HighContrast.roundedGrid jStar mu) r w)
                    (Homogenization.HighContrast.adaptedMean P
                      (Homogenization.HighContrast.roundedGrid jStar mu) r) ≤
                  ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.initGridConst Cd g E mu) ∧
                Homogenization.HighContrast.centeredMoment P
                    ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ)
                    (Homogenization.HighContrast.roundedGrid jStar mu) r ≤
                  ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.initGridConst Cd g E mu)) ∧
        -- the mean transport and the determinant increment
        (∀ mu : Homogenization.Mat d, mu.PosDef → ∀ r T : ℤ, r ≤ T →
            Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M r 0 →
              Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M T 0 →
              Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) T)
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.initGridConst Cd g E mu)
                    (Homogenization.HighContrast.adaptedMean P
                      (Homogenization.HighContrast.roundedGrid jStar mu) T)) ∧
                0 ≤ Homogenization.HighContrast.detIncrement P
                  (Homogenization.HighContrast.roundedGrid jStar mu) r T ∧
                Homogenization.HighContrast.detIncrement P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r T ≤
                  2 * (d : ℝ) *
                    Real.log
                      (Homogenization.HighContrast.initGridConst Cd g E mu)) ∧
        -- the identity grid
        (Homogenization.HighContrast.roundedGrid jStar (1 : Homogenization.Mat d) =
              (1 : Homogenization.Mat d) ∧
            1 ≤ Homogenization.HighContrast.initIdentityConst E ∧
            Homogenization.HighContrast.initIdentityConst E ≤
              24 * Homogenization.HighContrast.aspectRatio E ∧
            2 * (d : ℝ) *
                Real.log (Homogenization.HighContrast.initIdentityConst E) ≤
              CdQ * Real.log (2 + Homogenization.HighContrast.aspectRatio E) ∧
            ∀ r T : ℤ, jStar ≤ r → r ≤ T → T ≤ M →
              Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.blockScale (2 : ℝ)⁻¹
                    (Homogenization.HighContrast.blockSharp E))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r)
                  (Homogenization.HighContrast.blockScale 2 E) ∧
                Homogenization.HighContrast.centeredMoment P
                    ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ)
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r ≤
                  ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.initIdentityConst E) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) T)
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.initIdentityConst E)
                    (Homogenization.HighContrast.adaptedMean P
                      (Homogenization.HighContrast.roundedGrid jStar
                        (1 : Homogenization.Mat d)) T)) ∧
                0 ≤ Homogenization.HighContrast.detIncrement P
                  (Homogenization.HighContrast.roundedGrid jStar
                    (1 : Homogenization.Mat d)) r T ∧
                Homogenization.HighContrast.detIncrement P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r T ≤
                  2 * (d : ℝ) *
                    Real.log (Homogenization.HighContrast.initIdentityConst E))
    := by
  exact Homogenization.HighContrast.Initialization.random_source_adapted_initialization_assembly d hd g hg
