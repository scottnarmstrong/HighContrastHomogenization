/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.SourceControl.ReferenceIntermediate
import HCPoly.Provider.SourceControl.ResponseRow
import HCPoly.Provider.Transport.WindowBelowStart
import HCPoly.Provider.Transport.WindowCellMoments
import HCPoly.Provider.Transport.WindowCenteredSup
import HCPoly.Provider.Transport.WindowDefinedness
import HCPoly.Provider.Transport.WindowMomentBound
import HCPoly.Provider.Transport.WindowTerminalNormalization
import HCPoly.Provider.Transport.WindowWholeCell

/-!
# The assembly of `e.source.adapted.bound`

Random-source control in one bounded window, composed from the window
development.  The dimensional constant of the centered suprema is exhibited: the
witness is `C_{d,Q} = 2 (2d)^{1/Q}`, the operator-versus-Schatten factor in
dimension `2d`, which is what the centered `L^Q` and Orlicz estimates of the
whole-cell regime are proved at.

The composition is clause by clause.  The universal cell moments and their mixed
source tails are the window's cell-moment bundle, read at the rounded grid the
coupled window supplies for each positive definite shape; they are proved there
at every exponent, so the printed restriction to `[1, Q]` is a weakening.  The
all-earlier response row in partial-sum form is the burn-retaining annealed cell
bound summed as a geometric series, in both orientations.  The terminal mean's
definedness, positive definiteness, two-sided comparison and normalization are
the window's terminal package; its reference comparison is the printed
intermediate `κ_𝐄 ≤ 1 + 6(Θ - 1) ≤ 6 Π`, read at the reference block of the
coarse ellipticity assumption; the terminal loss is the coupled window's moment
bound on the multiplier.  The bridged normalization, the whole-cell regime and
the below-start quantity are the corresponding window estimates, read at the
bridged terminal matrix.

There are no definitions in this file.
-/

theorem Homogenization.HighContrast.SourceControl.random_source_control_assembly
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
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨2 * (2 * d : ℝ) ^ Q⁻¹, by positivity, ?_⟩
  intro Cd hCd P E Ψ K S hPprob _hstat hdag jStar M hw Y hY rho hrho l0 Khop _hKhop
    m m' mr hm hm' hmr _hgrid j hj W _hWcount hWmem hWcont t hjt hcontT
  haveI := hPprob
  have hE : Homogenization.IsSymmetricBlockMat E := hdag.refBlock_isSymm
  have hEpd : Homogenization.Book.Ch02.BlockPosDef E := hdag.refBlock_posDef
  have hg1 : g < 1 := hg.2
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hQ1 : (1 : ℝ) ≤ Q := le_trans one_le_two hQ
  have hqm :=
    Homogenization.HighContrast.Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hm
  have hqm' :=
    Homogenization.HighContrast.Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hm'
  have hqmr :=
    Homogenization.HighContrast.Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmr
  have hjt' : jStar ≤ t := le_trans hj hjt
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- A. the universal cell moments and their mixed source tails
    intro nu hnu aSc y hcont
    have hq :=
      Homogenization.HighContrast.Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hnu
    obtain ⟨h1, h2, h3, h4⟩ :=
      Homogenization.HighContrast.Transport.cell_moments_of_isWindowMultiplier hCd0.le hg1 hE
        hEpd hY hnu hq aSc y hcont
    exact ⟨fun p _ _ => h1 p, fun p _ _ => h2 p, h3, h4⟩
  · -- B. the all-earlier response row, in partial-sum form
    exact Homogenization.HighContrast.SourceControl.response_row_of_isWindowMultiplier hCd0.le hg1
      hE hEpd hY hm hqm t
  · -- C. the terminal mean, its comparison, its normalization, its loss
    exact ⟨Homogenization.HighContrast.Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY
        hmr hqmr hjt' hcontT,
      Homogenization.HighContrast.Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hmr
        hqmr hjt' hcontT,
      Homogenization.HighContrast.Transport.blockScale_inv_blockSharp_le_adaptedMean hCd0 hg1 hE
        hEpd hY hmr hqmr hjt' hcontT,
      Homogenization.HighContrast.Transport.adaptedMean_le_blockScale hE hY hmr hqmr hjt' hcontT,
      Homogenization.HighContrast.Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one_of_coarseEllipticityDagger
        hdag,
      Homogenization.HighContrast.Initialization.one_add_six_mul_refContrast_sub_one_le_six_mul_aspectRatio_of_coarseEllipticityDagger
        hdag,
      Homogenization.HighContrast.Transport.blockSize_adaptedMean_le hCd0 hg1 hE hEpd hY hmr hqmr
        hjt' hcontT,
      (Homogenization.HighContrast.Transport.terminal_loss_of_isWindowMultiplier hQ1 hw hY).1,
      (Homogenization.HighContrast.Transport.terminal_loss_of_isWindowMultiplier hQ1 hw hY).2⟩
  · -- D, E, F, read through a bridged terminal normalization
    intro eta _heta0 heta1 F hFsym hFpd hFlow _hFhigh
    refine ⟨⟨Homogenization.HighContrast.Transport.blockSize_le_div_of_bridge hCd0 hg1 hE hEpd hY
        hmr hqmr hjt' hcontT heta1 hFsym hFpd hFlow,
      Homogenization.HighContrast.Transport.blockSize_blockReflect E F⟩, ?_, ?_⟩
    · -- E. the whole-cell regime
      intro _hearly
      refine ⟨Homogenization.HighContrast.Transport.ae_whole_cell_packet hY hm' hj hWmem hWcont,
        Homogenization.HighContrast.Transport.hasIntegrableCoarseBlock_of_mem hY hm' hqm' hWmem
          hWcont, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Homogenization.HighContrast.Transport.cellFamilyMeanSup_le hCd0.le hg1 hE hEpd hY
          hm' hqm' hFsym hFpd hj hWmem hWcont
      · exact Homogenization.HighContrast.Transport.cellFamilyMeanSupAdjoint_le hCd0.le hg1 hE
          hEpd hY hm' hqm' hFsym hFpd hj hWmem hWcont
      · have h := Homogenization.HighContrast.Transport.eLpNorm_cellFamilyCenteredSup_le hCd0.le
          hg1 hE hY hm' hqm' hFsym hFpd hQ1 hj hWmem hWcont
        exact h.trans_eq (by ring_nf)
      · have h :=
          Homogenization.HighContrast.Transport.eLpNorm_cellFamilyCenteredSupAdjoint_le hCd0.le
            hg1 hE hY hm' hqm' hFsym hFpd hQ1 hj hWmem hWcont
        exact h.trans_eq (by ring_nf)
      · exact Homogenization.HighContrast.Transport.isShiftedBigOWithTop_cellFamilyCenteredSup
          hCd0.le hg1 hE hY hm' hqm' hFsym hFpd hQ1 hj hWmem hWcont
      · exact
          Homogenization.HighContrast.Transport.isShiftedBigOWithTop_cellFamilyCenteredSupAdjoint
            hCd0.le hg1 hE hY hm' hqm' hFsym hFpd hQ1 hj hWmem hWcont
    · -- F. the below-start quantity
      intro Z _hZcount hZcont
      exact Homogenization.HighContrast.Transport.below_start_of_isWindowMultiplier hCd0.le hg1
        hE hEpd hY hm hqm hFsym hFpd hrho t hZcont Q
