/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.BridgeConstant
import HCPoly.Provider.Bridge.LowerComparison
import HCPoly.Provider.Bridge.ShiftedDrift
import HCPoly.Provider.Bridge.UpperComparison
import HCPoly.Provider.Initialization.Structural

/-!
# The two-grid shifted-drift assembly

The maximal and reverse hybrid fillings give the two comparison inequalities.
The same common structural constant absorbs the terminal normalization change
and the three rows of the shifted determinant drift.
-/

theorem Homogenization.HighContrast.Bridge.random_source_bridge_two_grid_shifted_drift_assembly
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
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hC1, hUrow, hUsrc, hLrow, hLsrc, hSeta, hSmass, hSdrift,
      hSsrc⟩ :=
    Homogenization.HighContrast.Bridge.exists_bridge_constant d g hg
  refine ⟨C, hC, ?_⟩
  intro Cd hCd P E Ψ K S hP hstat _hunit hdag jStar M hw Y hY
  let : MeasureTheory.IsProbabilityMeasure P := hP
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hE : Homogenization.IsSymmetricBlockMat E := hdag.refBlock_isSymm
  have hEpd : Homogenization.Book.Ch02.BlockPosDef E := hdag.refBlock_posDef
  have hQ : (1 : ℝ) ≤ (Homogenization.HighContrast.initExpQ d g : ℝ) := by
    exact le_trans (by norm_num)
      (Homogenization.HighContrast.Initialization.two_le_initExpQ (d := d) hg)
  have hrho : 0 < Homogenization.HighContrast.initExpRhoDr g :=
    Homogenization.HighContrast.Bridge.initExpRhoDr_pos hg
  have hrhoSub : Homogenization.HighContrast.initExpRhoDr g < 1 - g :=
    Homogenization.HighContrast.Bridge.initExpRhoDr_lt_one_sub hg
  have hrho1 : Homogenization.HighContrast.initExpRhoDr g < 1 := by
    linarith only [hrhoSub, hg0]
  intro mp mv hmp hmv nn l hjn hsep hsmall hcont
  have hKpv : 1 ≤ Homogenization.HighContrast.gridRatio
      (Homogenization.HighContrast.roundedGrid jStar mp)
      (Homogenization.HighContrast.roundedGrid jStar mv) :=
    Homogenization.HighContrast.Transport.one_le_gridRatio _ _
  have hlpos : 0 < l :=
    Homogenization.HighContrast.Bridge.shift_pos_of_scale_separation hC hKpv hsep
  have hl0 : 0 ≤ l := le_of_lt hlpos
  refine ⟨?_, ?_, ?_⟩
  · exact Homogenization.HighContrast.Bridge.upper_comparison hd hCd hg0 hg1 hE hEpd
      hstat hQ hw hY hC.le hUrow hUsrc hmp hmv hrho.le hrho1.le hrhoSub.le hl0
      hjn hcont
  · exact Homogenization.HighContrast.Bridge.lower_comparison hd hCd hg0 hg1 hE hEpd
      hstat hQ hw hY hC.le hLrow hLsrc hmp hmv hrho.le hrho1.le hrhoSub.le hl0
      (by omega) hsmall hcont
  · intro eta heta0 heta4 hBA
    exact Homogenization.HighContrast.Bridge.shifted_drift hd hCd hg0 hg1 hE hEpd
      hstat hQ hw hY hC1 hrho hrho1 hrhoSub.le hSeta hSmass hSdrift hSsrc
      hmp hmv hlpos hjn heta0 heta4 hBA hcont
