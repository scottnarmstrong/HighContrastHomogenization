/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.PreYoungDischargeAssembly
import HCPoly.Provider.Response.RandomAdaptedResponseConditional

/-!
# Random adapted-response assembly

The unconditional pre-Young response families close the fixed-window adapted
response argument.  There are no new definitions in this file.
-/

open Homogenization Homogenization.HighContrast
  Homogenization.HighContrast.Response MeasureTheory

theorem Homogenization.HighContrast.Response.random_adapted_response_assembly
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (deltaAd : ℝ) (hdeltaAdLo : 0 < deltaAd) (hdeltaAdHi : deltaAd ≤ 1) :
    ∀ Cd : ℝ, 1 ≤ Cd →
    ∃ (epsCal deltaDet : ℝ) (H : ℕ) (eta etaDr : ℝ),
      -- the response parameters, in their pre-law order
      0 < epsCal ∧ epsCal ≤ 1 / 3 ∧ 0 < deltaDet ∧ deltaDet ≤ 1 ∧ 4 ≤ H ∧
        0 < eta ∧ eta ≤ 1 / 2 ∧ 0 < etaDr ∧ etaDr ≤ min 1 (eta / 2) ∧
        ∀ Arad : ℝ, 0 ≤ Arad →
        ∃ Bresp : ℝ, 0 < Bresp ∧
          -- the slack in the source exponent
          1 + 2 * Arad < Homogenization.HighContrast.initExpRhoMax d g * Bresp ∧
          -- the smallness of the terminal source contribution
          24 * (Cd * Homogenization.HighContrast.zetaG g) ^ 2 *
              (3 : ℝ) ^
                (1 + 2 * Arad -
                  Homogenization.HighContrast.initExpRhoMax d g * Bresp) ≤
            1 / 2 * eta ^ ((Homogenization.HighContrast.initExpQ d g : ℝ)⁻¹) ∧
          -- the smallness of the source row
          24 * (Cd * Homogenization.HighContrast.zetaG g) ^ 2 /
                ((3 : ℝ) ^ (3 / 2 - g) - 1) *
              (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ 1 ∧
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
                Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar
                  M Y →
                -- the moment bound for the source multiplier
                1 ≤ ∫ a, Y a ∂P →
                ENNReal.ofReal (∫ a, Y a ∂P) ≤
                  Homogenization.HighContrast.lqNorm P
                    (Homogenization.HighContrast.initExpQ d g : ℝ) Y →
                Homogenization.HighContrast.lqNorm P
                    (Homogenization.HighContrast.initExpQ d g : ℝ) Y ≤ 2 →
                ∀ (E0 : Homogenization.BlockMat d)
                  (m0 q : Homogenization.Mat d) (s t : ℤ),
                  Homogenization.IsSymmetricBlockMat E0 →
                  Homogenization.Book.Ch02.BlockPosDef E0 →
                  -- `e.global.selection.scales`
                  m0 = Homogenization.HighContrast.canonicalMetric E0 →
                  q = Homogenization.HighContrast.roundedGrid jStar m0 →
                  jStar ≤ s → t = s + (H : ℤ) → (H : ℤ) < t →
                  -- every queried cell lies in the window
                  (∀ k : ℤ, jStar ≤ k → k ≤ t →
                    Homogenization.HighContrast.adaptedCell q k ⊆
                      Homogenization.HighContrast.centeredCube d M) →
                  (∀ k : ℤ, k < jStar → ∀ v : ℤ, v = s ∨ v = t →
                    ∀ z ∈ Homogenization.HighContrast.containedCenters q k v,
                      Homogenization.HighContrast.adaptedCellTranslate q k z ⊆
                        Homogenization.HighContrast.centeredCube d M) →
                  -- the annealed blocks are finite and positive, and decrease
                  -- with the generation
                  (∀ k : ℤ, jStar ≤ k → k ≤ t →
                    Homogenization.HighContrast.HasFiniteAdaptedMean P q k ∧
                      Homogenization.Book.Ch02.BlockPosDef
                        (Homogenization.HighContrast.adaptedMean P q k)) →
                  (∀ k : ℤ, jStar ≤ k → k ≤ t →
                    Homogenization.BlockMatLoewnerLE
                      (Homogenization.HighContrast.adaptedMean P q t)
                      (Homogenization.HighContrast.adaptedMean P q k)) →
                  -- the source data carried into the response estimate
                  Homogenization.HighContrast.IsWindowedSourceFields P g Cd E
                    jStar m0 s t Y →
                  -- the portable majorant of the terminal history
                  ∀ Cport : ℝ, 1 ≤ Cport →
                    Homogenization.HighContrast.portableHistory P
                          (Homogenization.HighContrast.initExpQ d g : ℝ)
                          (Homogenization.HighContrast.initExpA g)
                          (Homogenization.HighContrast.initExpRhoMax d g) q jStar
                          t ≤
                        ENNReal.ofReal Cport *
                          Homogenization.HighContrast.portableProfile P
                            (Homogenization.HighContrast.initExpQ d g : ℝ)
                            (Homogenization.HighContrast.initExpA g)
                            (Homogenization.HighContrast.initExpRhoMax d g) q
                            jStar s t →
                    -- the block orders and determinant ratio at the response endpoints
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.adaptedMean P q t)
                        (Homogenization.HighContrast.adaptedMean P q s) →
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.blockSharp
                          (Homogenization.HighContrast.adaptedMean P q s))
                        (Homogenization.HighContrast.adaptedMean P q s) →
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.blockSharp
                          (Homogenization.HighContrast.adaptedMean P q t))
                        (Homogenization.HighContrast.adaptedMean P q t) →
                    Homogenization.HighContrast.adaptedDetRoot P q s <
                      (1 + deltaDet) *
                        Homogenization.HighContrast.adaptedDetRoot P q t →
                    -- the base-block calibration `e.global.selection.calibration`
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.blockScale (1 - epsCal) E0)
                        (Homogenization.HighContrast.adaptedMean P q s) →
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.adaptedMean P q s)
                        (Homogenization.HighContrast.blockScale (1 + epsCal)
                          E0) →
                    -- the downstream determinant caps and the determinant
                    -- ratio at the two endpoints
                    ∀ deltaDetBar deltaTerm : ℝ,
                      0 < deltaDetBar → deltaDetBar ≤ deltaDet →
                      0 < deltaTerm → deltaTerm ≤ deltaDetBar →
                      Homogenization.HighContrast.adaptedDetRoot P q s <
                        (1 + deltaTerm) *
                          Homogenization.HighContrast.adaptedDetRoot P q t →
                      -- the drift input at the two endpoints
                      Homogenization.HighContrast.linearDrift P
                            (Homogenization.HighContrast.initExpRhoDr g) q jStar
                            s +
                          Homogenization.HighContrast.linearDrift P
                            (Homogenization.HighContrast.initExpRhoDr g) q jStar
                            t ≤
                        etaDr →
                      -- the retained history input
                      ∀ etaProfBar etaIn etaOut epsSt : ℝ,
                        0 < etaProfBar →
                        etaProfBar ≤
                          (2 : ℝ) ^
                              (-(Homogenization.HighContrast.initExpQ d g : ℤ)) *
                            eta →
                        Homogenization.HighContrast.portableProfile P
                            (Homogenization.HighContrast.initExpQ d g : ℝ)
                            (Homogenization.HighContrast.initExpA g)
                            (Homogenization.HighContrast.initExpRhoMax d g) q
                            jStar s t ≤ ENNReal.ofReal etaOut →
                        ENNReal.ofReal Cport *
                            Homogenization.HighContrast.portableProfile P
                              (Homogenization.HighContrast.initExpQ d g : ℝ)
                              (Homogenization.HighContrast.initExpA g)
                              (Homogenization.HighContrast.initExpRhoMax d g) q
                              jStar s t ≤ ENNReal.ofReal epsSt →
                        max (max etaIn etaOut) epsSt ≤ etaProfBar →
                        -- `e.global.selection.eccentricity`
                        Homogenization.HighContrast.kappaRef E ≤
                          6 * Homogenization.HighContrast.aspectRatio E →
                        Homogenization.HighContrast.witnessEccentricity m0 ≤
                          (2 + Homogenization.HighContrast.aspectRatio E) ^
                            Arad →
                        jStar +
                            ⌈Bresp *
                              Real.logb 3
                                (2 +
                                  Homogenization.HighContrast.aspectRatio E)⌉ ≤
                          s →
                        -- `e.response.adapted.conclusion`
                        Homogenization.HighContrast.blockImbalance
                            (Homogenization.HighContrast.adaptedMean P q t) ≤
                          1 + deltaAd
    := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cpre, hCpre, hfamilies⟩ :=
    exists_pre_young_response_families d
  intro Cd hCd
  obtain ⟨epsCal, deltaDet, H, eta, etaDr, hc1, hc2, hc3, hc4,
      hc5, hc6, hc7, hc8, hc9, hresponse⟩ :=
    random_adapted_response_assembly_of_pre_young d hd g hg deltaAd
      hdeltaAdLo hdeltaAdHi Cpre hCpre Cd hCd
  refine ⟨epsCal, deltaDet, H, eta, etaDr, hc1, hc2, hc3, hc4, hc5,
    hc6, hc7, hc8, hc9, ?_⟩
  intro Arad hArad
  obtain ⟨Bresp, hB0, hB1, hB2, hB3, hsource⟩ :=
    hresponse Arad hArad
  refine ⟨Bresp, hB0, hB1, hB2, hB3, ?_⟩
  intro P E Psi Ksrc Ssrc hP hstat hunit hdag jStar M hwin Y hY hYone
    hYmean hYnorm E0 m0 q s t hE0symm hE0pd hm0eq hqeq hjs ht hHt
    hcells hbelow hblocks hmean hfields Cport hCport hportable hts hsSharp
    htSharp hdet hcalLo hcalHi deltaDetBar deltaTerm hddb0 hddb1 hdt0
    hdt1 hdetTerm hdrift etaProfBar etaIn etaOut epsSt hetaProfPos
    hetaProfCap hprofile hprofileScaled hprofileMax hkap hecc hbuf
  let : IsProbabilityMeasure P := hP
  have hE0full : (toFullBlockMat E0).PosDef :=
    posDef_toFullBlockMat hE0symm hE0pd
  have hm0pd : m0.PosDef := by
    rw [hm0eq]
    exact ShortHop.posDef_canonicalMetric hE0full
  have hgrid : IsRoundedGrid jStar q :=
    isRoundedGrid_of_eq_roundedGrid_of_isCoupledWindow hwin hm0pd hqeq
  have hpairs := hfamilies hstat hY hm0pd hqeq hgrid hjs H ht hbelow hblocks
  have hconditional := hsource P E Psi Ksrc Ssrc hP hstat hunit hdag
    jStar M hwin Y hY hYone hYmean hYnorm E0 m0 q s t hE0symm hE0pd
    hm0eq hqeq hjs ht hHt hcells hbelow hblocks hmean hfields Cport hCport
    hportable hts hsSharp htSharp hdet hcalLo hcalHi deltaDetBar deltaTerm
    hddb0 hddb1 hdt0 hdt1 hdetTerm hdrift etaProfBar etaIn etaOut epsSt
    hetaProfPos hetaProfCap hprofile hprofileScaled hprofileMax hkap hecc
    hbuf
  dsimp only at hconditional
  exact hconditional hpairs.1 hpairs.2
