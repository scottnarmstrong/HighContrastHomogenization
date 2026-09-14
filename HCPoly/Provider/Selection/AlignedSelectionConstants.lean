/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.BridgeAssembly
import HCPoly.Provider.Selection.BridgeConstantMonotonicity
import HCPoly.Provider.Transport.RandomSourceGridTransportAssembly

/-!
# Aligned analytic providers for selection

The grid-transport and shifted-drift estimates initially provide independent
constants.  Their upward closure permits both conclusions to be retained at
one common constant before the selector's remaining choices are made.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

noncomputable section

/-- The transport data and the full shifted-drift law are simultaneously
available at one common enlarged constant. -/
theorem exists_alignedTransportAndDriftConstant
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Khop : ℝ) (hKhop : 1 ≤ Khop) :
    ∃ Ltr : ℕ, ∃ Ctr : ℝ,
      TransportProviderData d g (initExpQ d g) (initExpRhoMax d g)
          (initExpA g) Khop Ctr Ltr ∧
        ∀ Cd : ℝ, 1 ≤ Cd →
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Psi : ℝ → ℝ)
          (K : ℝ) (source : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
          HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K source →
          ∀ jStar M : ℤ,
            IsCoupledWindow d (initExpQ d g : ℝ) K jStar M →
            ∀ Y : CoeffSpace d → ℝ,
              IsWindowMultiplier P g E Psi K Cd jStar M Y →
              ∀ mp mv : Mat d, mp.PosDef → mv.PosDef →
                ∀ nn l : ℤ, jStar ≤ nn - l →
                  Ctr * (1 + Real.log (gridRatio (roundedGrid jStar mp)
                    (roundedGrid jStar mv))) ≤ (l : ℝ) →
                  Ctr * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
                    (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
                  (∀ r : Mat d,
                    r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
                    ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
                      adaptedCell r j ⊆ centeredCube d M) →
                  BlockMatLoewnerLE
                      (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
                        (adaptedMean P (roundedGrid jStar mp) (nn - l)))
                      (blockScale (bridgeErrUpper Ctr Cd g (initExpRhoDr g)
                        (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
                        P E jStar mp mv nn l)
                        (adaptedMean P (roundedGrid jStar mp) nn)) ∧
                    BlockMatLoewnerLE
                      (blockScale (-bridgeErrLower Ctr Cd g (initExpRhoDr g)
                        (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
                        P E jStar mp mv nn l)
                        (adaptedMean P (roundedGrid jStar mp) (nn + l)))
                      (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
                        (adaptedMean P (roundedGrid jStar mp) (nn + l))) ∧
                    ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
                      BlockMatLoewnerLE
                        (blockScale (1 - eta)
                          (adaptedMean P (roundedGrid jStar mp) (nn + l)))
                        (adaptedMean P (roundedGrid jStar mv) nn) →
                      linearDrift P (initExpRhoDr g) (roundedGrid jStar mv)
                          jStar nn ≤
                        Ctr * (eta +
                          gridRatio (roundedGrid jStar mp)
                              (roundedGrid jStar mv) *
                            (3 : ℝ) ^ (-(l : ℝ)) +
                          (1 + gridRatio (roundedGrid jStar mp)
                              (roundedGrid jStar mv)) *
                            (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                            linearDrift P (initExpRhoDr g)
                              (roundedGrid jStar mp) jStar (nn + l) +
                          bridgeShiftedRemainder Ctr Cd g (initExpRhoDr g) E
                            jStar mp mv nn l) := by
  obtain ⟨Ltr, hLtr, Ctransport, hCtransport, htransport⟩ :=
    Transport.random_source_grid_transport_assembly d hd g hg (initExpQ d g)
      (two_le_initExpQ hg) (initExpQ_even d g) (initExpRhoMax d g)
      (initExpRhoMax_gt hg) (initExpRhoMax_lt_one hg) (initExpA g)
      (initExp_balance hg).symm (initExpA_pos hg) (initExpA_lt_one_sub hg)
      (initExp_summability_pos hd hg) Khop hKhop
  obtain ⟨Cbridge, hCbridge, hbridge⟩ :=
    Bridge.random_source_bridge_two_grid_shifted_drift_assembly d hd g hg
  let Ctr : ℝ := max Ctransport Cbridge
  let raw : TransportProviderData d g (initExpQ d g) (initExpRhoMax d g)
      (initExpA g) Khop Ctransport Ltr := ⟨hLtr, hCtransport, htransport⟩
  have htransport' : TransportProviderData d g (initExpQ d g)
      (initExpRhoMax d g) (initExpA g) Khop Ctr Ltr :=
    raw.enlargeConstant (le_max_left _ _)
  refine ⟨Ltr, Ctr, htransport', ?_⟩
  intro Cd hCd P E Psi K source hprob hstat hunit hdag jStar M hwin Y hY
  have : IsProbabilityMeasure P := hprob
  have hraw := hbridge Cd hCd P E Psi K source hprob hstat hunit hdag
    jStar M hwin Y hY
  exact twoGridShiftedDrift_enlargeConstant hd hCbridge (le_max_right _ _)
    (zero_le_one.trans hCd) hg.2 hstat hwin hY hraw

end

end Homogenization.HighContrast.Selection
