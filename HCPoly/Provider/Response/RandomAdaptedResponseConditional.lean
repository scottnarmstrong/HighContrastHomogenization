/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseProfileSpecialization
import HCPoly.Provider.Response.RandomAdaptedResponseAssembly
import HCPoly.Provider.Response.SourceBuffer

/-!
# Conditional adapted-response assembly

The assumed compact pre-Young estimates are carried at their raw response
functionals. All remaining constants are selected internally.
-/

open Homogenization Homogenization.HighContrast MeasureTheory

open scoped ENNReal Matrix MatrixOrder

noncomputable section

namespace Homogenization.HighContrast.Response

open Book.Ch02

set_option linter.unusedVariables false in
/-- The adapted-response endgame conditional on the two assumed compact
pre-Young estimates. -/
theorem random_adapted_response_assembly_of_pre_young :
  ∀ (d : ℕ), 2 ≤ d → ∀ (g : ℝ), g ∈ Set.Ico (0 : ℝ) 1 →
  ∀ (deltaAd : ℝ), 0 < deltaAd → deltaAd ≤ 1 →
  ∀ Cpre : ℝ, 1 ≤ Cpre →
  ∀ Cd : ℝ, 1 ≤ Cd →
  ∃ (epsCal deltaDet : ℝ) (H : ℕ) (eta etaDr : ℝ),
    0 < epsCal ∧ epsCal ≤ 1 / 3 ∧ 0 < deltaDet ∧ deltaDet ≤ 1 ∧ 4 ≤ H ∧
      0 < eta ∧ eta ≤ 1 / 2 ∧ 0 < etaDr ∧ etaDr ≤ min 1 (eta / 2) ∧
      ∀ Arad : ℝ, 0 ≤ Arad →
      ∃ Bresp : ℝ, 0 < Bresp ∧
        1 + 2 * Arad < initExpRhoMax d g * Bresp ∧
        24 * (Cd * zetaG g) ^ 2 *
            (3 : ℝ) ^ (1 + 2 * Arad - initExpRhoMax d g * Bresp) ≤
          1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹) ∧
        24 * (Cd * zetaG g) ^ 2 /
              ((3 : ℝ) ^ (3 / 2 - g) - 1) *
            (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ 1 ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Psi : ℝ → ℝ)
          (K : ℝ) (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
          HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
          ∀ jStar M : ℤ,
            ∀ (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar M),
            ∀ Y : CoeffSpace d → ℝ,
              IsWindowMultiplier P g E Psi K Cd jStar M Y →
              1 ≤ ∫ a, Y a ∂P →
              ENNReal.ofReal (∫ a, Y a ∂P) ≤
                lqNorm P (initExpQ d g : ℝ) Y →
              lqNorm P (initExpQ d g : ℝ) Y ≤ 2 →
              ∀ (E0 : BlockMat d) (m0 q : Mat d) (s t : ℤ),
                ∀ (hE0symm : IsSymmetricBlockMat E0)
                  (hE0pd : BlockPosDef E0)
                  (hm0eq : m0 = canonicalMetric E0)
                  (hqeq : q = roundedGrid jStar m0),
                jStar ≤ s → t = s + (H : ℤ) → (H : ℤ) < t →
                (∀ k : ℤ, jStar ≤ k → k ≤ t →
                  adaptedCell q k ⊆ centeredCube d M) →
                (∀ k : ℤ, k < jStar → ∀ v : ℤ, v = s ∨ v = t →
                  ∀ z ∈ containedCenters q k v,
                    adaptedCellTranslate q k z ⊆ centeredCube d M) →
                (∀ k : ℤ, jStar ≤ k → k ≤ t →
                  HasFiniteAdaptedMean P q k ∧
                    BlockPosDef (adaptedMean P q k)) →
                (∀ k : ℤ, jStar ≤ k → k ≤ t →
                  BlockMatLoewnerLE (adaptedMean P q t)
                    (adaptedMean P q k)) →
                IsWindowedSourceFields P g Cd E jStar m0 s t Y →
                ∀ Cport : ℝ, 1 ≤ Cport →
                  portableHistory P (initExpQ d g : ℝ) (initExpA g)
                        (initExpRhoMax d g) q jStar t ≤
                      ENNReal.ofReal Cport *
                        portableProfile P (initExpQ d g : ℝ) (initExpA g)
                          (initExpRhoMax d g) q jStar s t →
                  BlockMatLoewnerLE (adaptedMean P q t)
                    (adaptedMean P q s) →
                  BlockMatLoewnerLE (blockSharp (adaptedMean P q s))
                    (adaptedMean P q s) →
                  BlockMatLoewnerLE (blockSharp (adaptedMean P q t))
                    (adaptedMean P q t) →
                  adaptedDetRoot P q s <
                    (1 + deltaDet) * adaptedDetRoot P q t →
                  BlockMatLoewnerLE (blockScale (1 - epsCal) E0)
                    (adaptedMean P q s) →
                  BlockMatLoewnerLE (adaptedMean P q s)
                    (blockScale (1 + epsCal) E0) →
                  ∀ deltaDetBar deltaTerm : ℝ,
                    0 < deltaDetBar → deltaDetBar ≤ deltaDet →
                    0 < deltaTerm → deltaTerm ≤ deltaDetBar →
                    adaptedDetRoot P q s <
                      (1 + deltaTerm) * adaptedDetRoot P q t →
                    linearDrift P (initExpRhoDr g) q jStar s +
                        linearDrift P (initExpRhoDr g) q jStar t ≤ etaDr →
                    ∀ etaProfBar etaIn etaOut epsSt : ℝ,
                      0 < etaProfBar →
                      etaProfBar ≤ (2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta →
                      portableProfile P (initExpQ d g : ℝ) (initExpA g)
                          (initExpRhoMax d g) q jStar s t ≤
                        ENNReal.ofReal etaOut →
                      ENNReal.ofReal Cport *
                          portableProfile P (initExpQ d g : ℝ) (initExpA g)
                            (initExpRhoMax d g) q jStar s t ≤
                        ENNReal.ofReal epsSt →
                      max (max etaIn etaOut) epsSt ≤ etaProfBar →
                      kappaRef E ≤ 6 * aspectRatio E →
                      witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad →
                      jStar +
                          ⌈Bresp * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s →
                      let hE0full : (toFullBlockMat E0).PosDef :=
                        posDef_toFullBlockMat hE0symm hE0pd
                      let hm0pd : m0.PosDef := by
                        rw [hm0eq]
                        exact ShortHop.posDef_canonicalMetric hE0full
                      let hgrid : IsRoundedGrid jStar q :=
                        isRoundedGrid_of_eq_roundedGrid_of_isCoupledWindow
                          hwin hm0pd hqeq
                      let hqpd := Recurrence.posDef_of_isRoundedGrid hgrid
                      (∀ (hpreYoungMinus : ∀ Cresp, Cpre ≤ Cresp →
                          ∀ (h0 : {h : Mat d // IsSkewMat h})
                            (p r : Vec d),
                        let X := profilePrimalCenter P hqpd t
                          (fun a ↦ a.subSkew h0 h0.property) p r
                        let tau := profilePrimalResponseDefect P hqpd h0
                          h0.property s t p r
                        let EJ := ∫ a, responseJ (adaptedDomain hqpd t)
                          ((a.subSkew h0 h0.property).coeffOn
                            (adaptedDomain hqpd t)) p r ∂P
                        let row := profilePrimalHattedEarlierRow P q h0 s
                          X.1 X.2
                        let weak := profilePrimalWeakQuantity P m0 hqpd t
                          (fun a ↦ a.subSkew h0 h0.property) p r
                        let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
                          (fun i ↦ ∫ a, averageGradient
                            (adaptedDomain hqpd t)
                            ((a.subSkew h0 h0.property).coeffOn
                              (adaptedDomain hqpd t))
                            (centeredResponseOptimizer
                              (adaptedDomain hqpd t)
                              (a.subSkew h0 h0.property) p r) i ∂P)
                          (fun i ↦ ∫ a, averageFlux
                            (adaptedDomain hqpd t)
                            ((a.subSkew h0 h0.property).coeffOn
                              (adaptedDomain hqpd t))
                            (centeredResponseOptimizer
                              (adaptedDomain hqpd t)
                              (a.subSkew h0 h0.property) p r) i ∂P)
                        ENNReal.ofReal |Jtilde| ≤
                          ENNReal.ofReal Cresp *
                              ENNReal.ofReal (Real.sqrt tau) *
                            (ENNReal.ofReal (Real.sqrt tau) +
                              ENNReal.ofReal (Real.sqrt EJ) +
                              row ^ (1 / 2 : ℝ)) +
                          ENNReal.ofReal Cresp *
                              ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
                              ENNReal.ofReal (Real.sqrt EJ) *
                            (ENNReal.ofReal (Real.sqrt EJ) +
                              row ^ (1 / 2 : ℝ)) +
                          ENNReal.ofReal Cresp * weak),
                        ∀ (hpreYoungPlus : ∀ Cresp, Cpre ≤ Cresp →
                            ∀ (h0 : {h : Mat d // IsSkewMat h})
                              (p r : Vec d),
                          let X := profileAdjointCenter P hqpd t
                            (fun a ↦ a.subSkew h0 h0.property) p r
                          let tau := profileAdjointResponseDefect P hqpd h0
                            h0.property s t p r
                          let EJ := ∫ a, responseJ (adaptedDomain hqpd t)
                            ((a.subSkew h0 h0.property).transpose.coeffOn
                              (adaptedDomain hqpd t)) p r ∂P
                          let row := profileAdjointHattedEarlierRow P q h0 s
                            X.1 X.2
                          let weak := profileAdjointWeakQuantity P m0 hqpd t
                            (fun a ↦ a.subSkew h0 h0.property) p r
                          let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
                            (fun i ↦ ∫ a, averageGradient
                              (adaptedDomain hqpd t)
                              ((a.subSkew h0 h0.property).transpose.coeffOn
                                (adaptedDomain hqpd t))
                              (centeredAdjointOptimizer
                                (adaptedDomain hqpd t)
                                (a.subSkew h0 h0.property) p r) i ∂P)
                            (fun i ↦ ∫ a, averageFlux
                              (adaptedDomain hqpd t)
                              ((a.subSkew h0 h0.property).transpose.coeffOn
                                (adaptedDomain hqpd t))
                              (centeredAdjointOptimizer
                                (adaptedDomain hqpd t)
                                (a.subSkew h0 h0.property) p r) i ∂P)
                          ENNReal.ofReal |Jtilde| ≤
                            ENNReal.ofReal Cresp *
                                ENNReal.ofReal (Real.sqrt tau) *
                              (ENNReal.ofReal (Real.sqrt tau) +
                                ENNReal.ofReal (Real.sqrt EJ) +
                                row ^ (1 / 2 : ℝ)) +
                            ENNReal.ofReal Cresp *
                                ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
                                ENNReal.ofReal (Real.sqrt EJ) *
                              (ENNReal.ofReal (Real.sqrt EJ) +
                                row ^ (1 / 2 : ℝ)) +
                            ENNReal.ofReal Cresp * weak),
                          blockImbalance (adaptedMean P q t) ≤ 1 + deltaAd) := by
  classical
  intro d hd g hg deltaAd hdeltaAdLo _hdeltaAdHi Cpre _hCpre
  have : NeZero d := ⟨by omega⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let Cprof : ℝ := (exists_profile_response_constant hd).choose
  have hCprof : 1 ≤ Cprof :=
    (exists_profile_response_constant hd).choose_spec.1
  obtain ⟨Cresp, epsCal, deltaDet, H, eta, etaDr, hCrespEq, hCresp,
      hCprofResp, hCpreResp, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9,
      habs⟩ :=
    exists_merged_response_window (Cpre := Cpre) hd hg hdeltaAdLo hCprof
  subst Cresp
  intro Csrc hCsrc
  refine ⟨epsCal, deltaDet, H, eta, etaDr, hc1, hc2, hc3, hc4, hc5,
    hc6, hc7, hc8, hc9, ?_⟩
  intro Arad hArad
  obtain ⟨Bresp, hB0, hB1, hB2, hB3⟩ :=
    exists_bresp hd hg hCsrc hc6 Arad
  refine ⟨Bresp, hB0, hB1, hB2, hB3, ?_⟩
  intro P E Psi Ksrc Ssrc hP hstat hunit hdag jStar M hwin Y hY hYone
    hYmean hYnorm E0 m0 q s t hE0symm hE0pd hm0eq hqeq hjs ht hHt
    hcells hbelow hblocks hmean hfields Cport hCport hportable hts hsSharp
    htSharp hdet hcalLo hcalHi deltaDetBar deltaTerm _hddb0 _hddb1 _hdt0
    _hdt1 _hdetTerm hdrift etaProfBar etaIn etaOut epsSt hetaProfPos
    hetaProfCap hprofile hprofileScaled hprofileMax hkap hecc hbuf
  dsimp only
  intro hpreYoungMinus hpreYoungPlus
  let : IsProbabilityMeasure P := hP
  have hE0full : (toFullBlockMat E0).PosDef :=
    posDef_toFullBlockMat hE0symm hE0pd
  have hm0pd : m0.PosDef := by
    rw [hm0eq]
    exact ShortHop.posDef_canonicalMetric hE0full
  have hgrid : IsRoundedGrid jStar q :=
    isRoundedGrid_of_eq_roundedGrid_of_isCoupledWindow hwin hm0pd hqeq
  let hqpd := Recurrence.posDef_of_isRoundedGrid hgrid
  have hspec0 := profile_response_sup_of_pre_young hd hg Cpre Csrc hCsrc
    hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hArad hB0 hB1 hB2 hB3 hP hstat
    hunit hdag hwin hY hYone hYmean hYnorm hE0symm hE0pd hm0eq hqeq hjs
    ht hHt hcells hbelow hblocks hmean hfields hCport hportable hts hsSharp
    htSharp hdet hcalLo hcalHi hdrift hetaProfPos hetaProfCap hprofile
    hprofileScaled hprofileMax hkap hecc hbuf
  have hspec := hspec0 hpreYoungMinus hpreYoungPlus
  dsimp only at hspec
  let Cresp : ℝ := max Cprof Cpre
  let cconst : ℝ := (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹
  let GammaStar : ℝ := 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1
  let cepsStar : ℝ := Real.sqrt 2
  let betaStar : ℝ := cepsStar * (1 + deltaDet) ^ ((d : ℝ) / 2)
  let chiTheta : ℝ := Real.sqrt (3 / 2) *
    (1 + deltaDet) ^ ((d : ℝ) / 2)
  let AStar : ℝ := 2 * chiTheta
  let TStar : ℝ := 2 * ((1 + deltaDet) ^ (d : ℝ) - 1) * chiTheta
  let LStar : ℝ := 32 * GammaStar * cepsStar * betaStar *
    (1 + deltaDet) ^ ((d : ℝ) / 2) * chiTheta
  let KStar : ℝ := Real.sqrt betaStar * (1 + deltaDet) ^ ((d : ℝ) / 4)
  let LenStar : ℝ := 2 * Real.sqrt chiTheta
  let LambdaStar : ℝ := Real.sqrt 5 * Real.sqrt chiTheta
  let Scen : ℝ := 2 * ∑ r ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-(1 / 2 - initExpRhoMax d g) * (r : ℝ))
  let Scell : ℝ := ∑ r ∈ Finset.Icc 1 H,
    (3 : ℝ) ^ (-(r : ℝ) / 2 +
      initExpA g * ((r : ℝ) - 1) / (initExpQ d g : ℝ))
  let Sav : ℝ := ∑ r ∈ Finset.Icc 1 H,
    (3 : ℝ) ^ (-initExpA g * (r : ℝ) +
      initExpA g * ((r : ℝ) - 1) / (2 * (initExpQ d g : ℝ)))
  let UStar : ℝ := (Scen + Scell) * eta ^ ((initExpQ d g : ℝ)⁻¹) +
    Sav * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹)
  let BStar : ℝ := (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) *
    eta ^ ((2 : ℝ)⁻¹)
  let RStar : ℝ := Cresp * KStar * LenStar * UStar +
    Cresp * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
      (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) +
    cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹)
  let omegaRsp : ℝ := 2 * Cresp *
    (TStar + Real.sqrt (TStar * AStar) + Real.sqrt (TStar * LStar) +
      (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar)) +
      RStar ^ 2)
  have hresponses : ∀ (S SStar K : Mat d), S.PosDef → SStar.PosDef →
      toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K →
      0 ≤ omegaRsp ∧
        sSup
            ((fun e : Vec d ↦
                |centeredResponse P (adaptedDomain hqpd t)
                    (centeredResponseLoadP S SStar K e)
                    (centeredResponseLoadQ S SStar K e -
                      responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| +
                |centeredAdjointResponse P (adaptedDomain hqpd t)
                    (centeredResponseLoadP S SStar K e)
                    (centeredResponseLoadQ S SStar K e +
                      responseSkew K *ᵥ centeredResponseLoadP S SStar K e)|) ''
              {e : Vec d | e ⬝ᵥ e = 1}) ≤
          omegaRsp * blockImbalance (adaptedMean P q s) := by
    simpa only [Cprof, Cresp, cconst, GammaStar, cepsStar, betaStar,
      chiTheta, AStar, TStar, LStar, KStar, LenStar, LambdaStar, Scen,
      Scell, Sav, UStar, BStar, RStar, omegaRsp, hqpd] using hspec.2
  have habsorb :
      12 * (d : ℝ) * omegaRsp * (1 + deltaDet) ^ (2 * (d : ℝ)) *
        (1 + deltaAd⁻¹) < 1 :=
    habs cconst GammaStar cepsStar betaStar chiTheta AStar TStar LStar
      KStar LenStar LambdaStar Scen Scell Sav UStar BStar RStar omegaRsp
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl
  have hEtPos : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
      (hblocks t (by omega) le_rfl).2
  obtain ⟨S0, SStar0, K0, hS0, hStar0, hform0⟩ :=
    exists_schurBlock hEtPos
  have homega : 0 ≤ omegaRsp :=
    (hresponses S0 SStar0 K0 hS0 hStar0 hform0).1
  apply random_adapted_response_endgame hd hqpd hE0symm hE0pd
    (hblocks t (by omega) le_rfl).1
    (hblocks s hjs (by omega)).2
    (hblocks t (by omega) le_rfl).2
    hts hsSharp htSharp hc1 hc2 hcalLo hcalHi hdet hc3.le
    hdeltaAdLo homega habsorb
  intro S SStar K hS hStar hform
  exact (hresponses S SStar K hS hStar hform).2


end Homogenization.HighContrast.Response
