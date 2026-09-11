/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SourceObjects
import HCPoly.Provider.SourceControl.SourceControlAssembly

/-!
# The source estimate on adapted cubes `e.source.adapted.bound` — the windowed control core

Random-source control in one bounded window.  Unit range of dependence is **not**
assumed: the hypotheses are stationarity and the coarse ellipticity assumption
with its gauge and source scale, exactly the random-source data of 02, together
with a coupled window pair and the common multiplier of the window.

This candidate carries the blocks of the printed proposition that do not read
the maximal filling of `l.two.grid.whitney`: the universal cell
moments and their mixed source tails, the all-earlier response row, the terminal
comparison and its normalizations, the whole-cell regime, and the below-start
quantity.  The continued-regime estimates for the cells below the burn, and the
retained filling assertions, are the remaining blocks; they quantify over the
selected cells of that lemma's filling and must be designed with it.

The multiplier is data.  The printed proposition says "let `Y_P` be the
multiplier of `e.source.multiplier`"; the corresponding Lean
hypothesis is that lemma's conclusion, carried by `IsWindowMultiplier`.  The
window, the grids, the scales and the cells are bound before it, which is the
determinism requirement of the printed statement.

The terminal mean's finiteness, positive definiteness and reference comparison
are concluded before the deterministic terminal matrix and its bridge parameter
are bound: those conclusions do not mention them, and a consumer that takes the
terminal matrix to be the terminal mean itself would otherwise have to supply
its positive definiteness in order to obtain it.

The convention that the supremum of an empty family of nonnegative quantities is
zero is the extended-real lattice's own, so the empty target family and the
empty below-start families — the degenerate instantiation the persistence
argument makes — are legal.
The dimensional constant of the source-control subsection is a parameter, not a
witness of this statement: it is fixed once, sufficiently large for the filling
and Whitney estimates, and produced by `e.source.multiplier`, which is
also what supplies the multiplier bound this statement binds.  Both the
hypothesis that names it and every conclusion that names it are monotone in it,
so quantifying it universally above one is the faithful reading of a constant
fixed before the subsection's results.
-/

theorem HCPoly.Frozen.random_source_control
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) (Q : ℝ) (hQ : 2 ≤ Q) :
    ∃ CdQ : ℝ, 0 < CdQ ∧
      ∀ Cd : ℝ, 1 ≤ Cd →
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
        (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ,
          Homogenization.HighContrast.IsCoupledWindow d Q K jStar M →
          ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
            Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M Y →
            ∀ rho : ℝ, g < rho →
              ∀ (l0 : ℕ) (Khop : ℝ), 1 ≤ Khop →
                ∀ m m' mr : Homogenization.Mat d,
                  m.PosDef → m'.PosDef → mr.PosDef →
                  Homogenization.HighContrast.gridRatio
                      (Homogenization.HighContrast.roundedGrid jStar m)
                      (Homogenization.HighContrast.roundedGrid jStar m') ≤ Khop →
                  ∀ j : ℤ, jStar ≤ j →
                    ∀ W : Set (Set (Homogenization.Vec d)), W.Countable →
                      (∀ V ∈ W, ∃ y : Homogenization.Vec d,
                        V = Homogenization.HighContrast.adaptedCellTranslate
                          (Homogenization.HighContrast.roundedGrid jStar m') j y) →
                      (∀ V ∈ W, V ⊆ Homogenization.HighContrast.centeredCube d M) →
                      ∀ t : ℤ, j ≤ t →
                        Homogenization.HighContrast.adaptedCell
                            (Homogenization.HighContrast.roundedGrid jStar mr) t ⊆
                          Homogenization.HighContrast.centeredCube d M →
        -- A. the universal cell moments and their mixed source tails
        (∀ n : Homogenization.Mat d, n.PosDef → ∀ (aSc : ℤ) (y : Homogenization.Vec d),
            Homogenization.HighContrast.adaptedCellTranslate
                (Homogenization.HighContrast.roundedGrid jStar n) aSc y ⊆
              Homogenization.HighContrast.centeredCube d M →
            (∀ p : ℝ, 1 ≤ p → p ≤ Q →
              Homogenization.HighContrast.lqNorm P p
                  (fun a => Homogenization.HighContrast.blockSize
                    (Homogenization.HighContrast.coarseBlock
                      (Homogenization.HighContrast.adaptedCellTranslate
                        (Homogenization.HighContrast.roundedGrid jStar n) aSc y) a)
                    E) ≤
                ENNReal.ofReal
                    (Homogenization.HighContrast.boundaryConst Cd g n *
                      Homogenization.HighContrast.burnDiscount g jStar aSc) *
                  Homogenization.HighContrast.lqNorm P p Y) ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ Q →
              Homogenization.HighContrast.lqNorm P p
                  (fun a => Homogenization.HighContrast.blockSize
                    (Homogenization.HighContrast.coarseStarInv
                      (Homogenization.HighContrast.adaptedCellTranslate
                        (Homogenization.HighContrast.roundedGrid jStar n) aSc y) a)
                    (Homogenization.blockReflect E)) ≤
                ENNReal.ofReal
                    (Homogenization.HighContrast.boundaryConst Cd g n *
                      Homogenization.HighContrast.burnDiscount g jStar aSc) *
                  Homogenization.HighContrast.lqNorm P p Y) ∧
            Homogenization.HighContrast.IsShiftedBigOWith P Ψ
              (fun a => Homogenization.HighContrast.blockSize
                (Homogenization.HighContrast.coarseBlock
                  (Homogenization.HighContrast.adaptedCellTranslate
                    (Homogenization.HighContrast.roundedGrid jStar n) aSc y) a) E)
              (Homogenization.HighContrast.boundaryConst Cd g n *
                Homogenization.HighContrast.burnDiscount g jStar aSc)
              (Homogenization.HighContrast.boundaryConst Cd g n *
                Homogenization.HighContrast.sourceRemainderScale d jStar K *
                Homogenization.HighContrast.burnDiscount g jStar aSc) ∧
            Homogenization.HighContrast.IsShiftedBigOWith P Ψ
              (fun a => Homogenization.HighContrast.blockSize
                (Homogenization.HighContrast.coarseStarInv
                  (Homogenization.HighContrast.adaptedCellTranslate
                    (Homogenization.HighContrast.roundedGrid jStar n) aSc y) a)
                (Homogenization.blockReflect E))
              (Homogenization.HighContrast.boundaryConst Cd g n *
                Homogenization.HighContrast.burnDiscount g jStar aSc)
              (Homogenization.HighContrast.boundaryConst Cd g n *
                Homogenization.HighContrast.sourceRemainderScale d jStar K *
                Homogenization.HighContrast.burnDiscount g jStar aSc)) ∧
        -- B. the all-earlier response row, in partial-sum form
        (∀ s : ℤ, jStar ≤ s → s < t →
          Homogenization.HighContrast.adaptedCell
              (Homogenization.HighContrast.roundedGrid jStar m) s ⊆
            Homogenization.HighContrast.centeredCube d M →
          ∀ lam : ℝ, g < lam →
            ∀ Ctr : ℤ → Finset (Fin d → ℤ),
              (∀ k : ℤ, k < jStar → ∀ w : Fin d → ℤ,
                w ∈ Ctr k ↔
                  Homogenization.HighContrast.adaptedCellCenter
                      (Homogenization.HighContrast.roundedGrid jStar m) k w ∈
                    Homogenization.HighContrast.adaptedCell
                      (Homogenization.HighContrast.roundedGrid jStar m) s) →
              ∀ Klo : ℤ, Klo < jStar → ∀ X : Homogenization.BlockVec d,
                ∑ k ∈ Finset.Ico Klo jStar,
                    (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) *
                      (((Ctr k).card : ℝ)⁻¹ *
                        ∑ w ∈ Ctr k,
                          Homogenization.blockVecDot X
                            (Homogenization.blockMatVecMul
                              (Homogenization.HighContrast.annealedBlock P
                                (Homogenization.HighContrast.adaptedCellAt
                                  (Homogenization.HighContrast.roundedGrid jStar m)
                                  k w)) X)) ≤
                  Homogenization.HighContrast.boundaryConst Cd g m *
                      (∫ a, Y a ∂P) / ((3 : ℝ) ^ (lam - g) - 1) *
                      (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) *
                    Homogenization.blockVecDot X
                      (Homogenization.blockMatVecMul E X) ∧
                ∑ k ∈ Finset.Ico Klo jStar,
                    (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) *
                      (((Ctr k).card : ℝ)⁻¹ *
                        ∑ w ∈ Ctr k,
                          Homogenization.blockVecDot X
                            (Homogenization.blockMatVecMul
                              (Homogenization.HighContrast.annealedStarInv P
                                (Homogenization.HighContrast.adaptedCellAt
                                  (Homogenization.HighContrast.roundedGrid jStar m)
                                  k w)) X)) ≤
                  Homogenization.HighContrast.boundaryConst Cd g m *
                      (∫ a, Y a ∂P) / ((3 : ℝ) ^ (lam - g) - 1) *
                      (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) *
                    Homogenization.blockVecDot X
                      (Homogenization.blockMatVecMul
                        (Homogenization.blockReflect E) X)) ∧
        -- C. the terminal mean, its comparison, its normalization, its loss
        (Homogenization.HighContrast.HasFiniteAdaptedMean P
              (Homogenization.HighContrast.roundedGrid jStar mr) t ∧
            Homogenization.Book.Ch02.BlockPosDef
              (Homogenization.HighContrast.adaptedMean P
                (Homogenization.HighContrast.roundedGrid jStar mr) t) ∧
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.blockScale
                (Homogenization.HighContrast.boundaryConst Cd g mr *
                  ∫ a, Y a ∂P)⁻¹
                (Homogenization.HighContrast.blockSharp E))
              (Homogenization.HighContrast.adaptedMean P
                (Homogenization.HighContrast.roundedGrid jStar mr) t) ∧
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.adaptedMean P
                (Homogenization.HighContrast.roundedGrid jStar mr) t)
              (Homogenization.HighContrast.blockScale
                (Homogenization.HighContrast.boundaryConst Cd g mr * ∫ a, Y a ∂P)
                E) ∧
            Homogenization.HighContrast.kappaRef E ≤
              1 + 6 * (Homogenization.HighContrast.refContrast E - 1) ∧
            1 + 6 * (Homogenization.HighContrast.refContrast E - 1) ≤
              6 * Homogenization.HighContrast.aspectRatio E ∧
            Homogenization.HighContrast.blockSize E
                (Homogenization.HighContrast.adaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mr) t) ≤
              Homogenization.HighContrast.kappaRef E *
                (Homogenization.HighContrast.boundaryConst Cd g mr * ∫ a, Y a ∂P) ∧
            ENNReal.ofReal (∫ a, Y a ∂P) *
                Homogenization.HighContrast.lqNorm P Q Y ≤
              Homogenization.HighContrast.lqNorm P Q Y ^ 2 ∧
            Homogenization.HighContrast.lqNorm P Q Y ^ 2 ≤ 4) ∧
        -- D, E. the estimates read through a bridged terminal normalization
        (∀ eta : ℝ, 0 ≤ eta → eta < 1 →
          ∀ F : Homogenization.BlockMat d,
            Homogenization.IsSymmetricBlockMat F →
            Homogenization.Book.Ch02.BlockPosDef F →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.blockScale (1 - eta)
                (Homogenization.HighContrast.adaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mr) t)) F →
            Homogenization.BlockMatLoewnerLE F
              (Homogenization.HighContrast.blockScale (1 + eta)
                (Homogenization.HighContrast.adaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mr) t)) →
            -- D. the bridged normalization and the adjoint normalization
            (Homogenization.HighContrast.blockSize E F ≤
                Homogenization.HighContrast.kappaRef E *
                  (Homogenization.HighContrast.boundaryConst Cd g mr *
                    ∫ a, Y a ∂P) / (1 - eta) ∧
              Homogenization.HighContrast.blockSize (Homogenization.blockReflect E)
                  (Homogenization.blockReflect F) =
                Homogenization.HighContrast.blockSize E F) ∧
            -- E. the whole-cell regime
            (j < jStar + (l0 : ℤ) →
              (∀ᵐ a ∂P, ∀ V ∈ W,
                Homogenization.BlockMatLoewnerLE
                    (Homogenization.HighContrast.coarseBlock V a)
                    (Homogenization.HighContrast.blockScale
                      (Homogenization.HighContrast.boundaryConst Cd g m' * Y a) E) ∧
                  Homogenization.BlockMatLoewnerLE
                    (Homogenization.HighContrast.coarseStarInv V a)
                    (Homogenization.HighContrast.blockScale
                      (Homogenization.HighContrast.boundaryConst Cd g m' * Y a)
                      (Homogenization.blockReflect E))) ∧
              (∀ V ∈ W, Homogenization.HighContrast.HasIntegrableCoarseBlock P V) ∧
              Homogenization.HighContrast.cellFamilyMeanSup P W F ≤
                ENNReal.ofReal
                  (Homogenization.HighContrast.boundaryConst Cd g m' *
                    (∫ a, Y a ∂P) * Homogenization.HighContrast.blockSize E F) ∧
              Homogenization.HighContrast.cellFamilyMeanSupAdjoint P W
                  (Homogenization.blockReflect F) ≤
                ENNReal.ofReal
                  (Homogenization.HighContrast.boundaryConst Cd g m' *
                    (∫ a, Y a ∂P) * Homogenization.HighContrast.blockSize E F) ∧
              MeasureTheory.eLpNorm
                  (Homogenization.HighContrast.cellFamilyCenteredSup P Q W F)
                  (ENNReal.ofReal Q) P ≤
                ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.boundaryConst Cd g m' *
                      Homogenization.HighContrast.blockSize E F) *
                  Homogenization.HighContrast.lqNorm P Q Y ∧
              MeasureTheory.eLpNorm
                  (Homogenization.HighContrast.cellFamilyCenteredSupAdjoint P Q W
                    (Homogenization.blockReflect F)) (ENNReal.ofReal Q) P ≤
                ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.boundaryConst Cd g m' *
                      Homogenization.HighContrast.blockSize E F) *
                  Homogenization.HighContrast.lqNorm P Q Y ∧
              Homogenization.HighContrast.IsShiftedBigOWithTop P Ψ
                (Homogenization.HighContrast.cellFamilyCenteredSup P Q W F)
                (CdQ * Homogenization.HighContrast.boundaryConst Cd g m' *
                  Homogenization.HighContrast.blockSize E F *
                  (2 + Homogenization.HighContrast.sourceRemainderScale d jStar K *
                    Homogenization.HighContrast.momentMultiplier 1
                      (Homogenization.HighContrast.growthBar K)))
                (CdQ * Homogenization.HighContrast.boundaryConst Cd g m' *
                  Homogenization.HighContrast.blockSize E F *
                  Homogenization.HighContrast.sourceRemainderScale d jStar K) ∧
              Homogenization.HighContrast.IsShiftedBigOWithTop P Ψ
                (Homogenization.HighContrast.cellFamilyCenteredSupAdjoint P Q W
                  (Homogenization.blockReflect F))
                (CdQ * Homogenization.HighContrast.boundaryConst Cd g m' *
                  Homogenization.HighContrast.blockSize E F *
                  (2 + Homogenization.HighContrast.sourceRemainderScale d jStar K *
                    Homogenization.HighContrast.momentMultiplier 1
                      (Homogenization.HighContrast.growthBar K)))
                (CdQ * Homogenization.HighContrast.boundaryConst Cd g m' *
                  Homogenization.HighContrast.blockSize E F *
                  Homogenization.HighContrast.sourceRemainderScale d jStar K)) ∧
            -- F. the below-start quantity
            (∀ Z : ℤ → Set (Homogenization.Vec d),
              (∀ k : ℤ, k < jStar → (Z k).Countable) →
              (∀ k : ℤ, k < jStar → ∀ z ∈ Z k,
                Homogenization.HighContrast.adaptedCellTranslate
                    (Homogenization.HighContrast.roundedGrid jStar m) k z ⊆
                  Homogenization.HighContrast.centeredCube d M) →
              (∀ᵐ a ∂P,
                  Homogenization.HighContrast.belowStartSup rho
                      (Homogenization.HighContrast.roundedGrid jStar m) jStar t Z F
                      a ≤
                    ENNReal.ofReal
                      (Homogenization.HighContrast.boundaryConst Cd g m * Y a *
                        Homogenization.HighContrast.blockSize E F *
                        (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))))) ∧
                (∫⁻ a,
                    Homogenization.HighContrast.belowStartSup rho
                      (Homogenization.HighContrast.roundedGrid jStar m) jStar t Z F a
                      ∂P) ≤
                  ENNReal.ofReal
                    (Homogenization.HighContrast.boundaryConst Cd g m *
                      (∫ a, Y a ∂P) * Homogenization.HighContrast.blockSize E F *
                      (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ)))) ∧
                MeasureTheory.eLpNorm
                    (Homogenization.HighContrast.belowStartSup rho
                      (Homogenization.HighContrast.roundedGrid jStar m) jStar t Z F)
                    (ENNReal.ofReal Q) P ≤
                  ENNReal.ofReal
                      (Homogenization.HighContrast.boundaryConst Cd g m *
                        Homogenization.HighContrast.blockSize E F *
                        (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ)))) *
                    Homogenization.HighContrast.lqNorm P Q Y ∧
                Homogenization.HighContrast.IsShiftedBigOWithTop P Ψ
                  (Homogenization.HighContrast.belowStartSup rho
                    (Homogenization.HighContrast.roundedGrid jStar m) jStar t Z F)
                  (Homogenization.HighContrast.boundaryConst Cd g m *
                    Homogenization.HighContrast.blockSize E F *
                    (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))))
                  (Homogenization.HighContrast.boundaryConst Cd g m *
                    Homogenization.HighContrast.blockSize E F *
                    Homogenization.HighContrast.sourceRemainderScale d jStar K *
                    (3 : ℝ) ^ (-rho * ((t : ℝ) - (jStar : ℝ))))))
    := by
  exact Homogenization.HighContrast.SourceControl.random_source_control_assembly d hd g hg Q hQ
