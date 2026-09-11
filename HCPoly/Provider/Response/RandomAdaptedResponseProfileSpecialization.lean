/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileResponseAssembly
import HCPoly.Provider.Response.RandomAdaptedResponseCompactInsertion
import HCPoly.Provider.Response.RandomAdaptedResponseProfileScalar
import HCPoly.Provider.Response.RandomAdaptedResponseCalibrationScalar
import HCPoly.Provider.Response.RandomAdaptedResponseCarrierBridge
import HCPoly.Provider.Response.RandomAdaptedResponseShiftedCarrier
import HCPoly.Provider.Response.RandomAdaptedResponseSignedEnergy
import HCPoly.Provider.Response.RandomAdaptedResponseDefectBridge
import HCPoly.Provider.Response.RandomAdaptedResponseRowWeakClosure
import HCPoly.Provider.Response.RandomAdaptedResponseLoadProducts
import HCPoly.Provider.Response.EndgameGlue
import HCPoly.Provider.Response.WindowAbsorption
import HCPoly.Provider.Persistence.AdaptedPersistence
import HCPoly.Provider.ShortHop.PathStep
import HCPoly.Provider.ShortHop.Normalization

/-!
# True-carrier terminal profile specialization

The profile theorem is specialized at arbitrary skew gauges and load pairs.
The eventual response endgame uses the internally extracted Schur gauge and
loads; neither the Schur decomposition nor calibrated scalar bounds are
premises of the public fixed-window theorem.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory Set

open scoped ENNReal Matrix MatrixOrder

noncomputable section

private theorem to_full_block_vec_pair {d : ℕ} (p r : Vec d) :
    toFullBlockVec ((p, r) : BlockVec d) = Sum.elim p r := by
  funext i
  cases i <;> rfl

/-- Source data and the two ruled compact estimates imply the literal
response supremum at every internally supplied Schur decomposition. -/
theorem profile_response_sup_of_pre_young
    {d : ℕ} (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Cpre Csrc : ℝ) {epsCal deltaDet eta etaDr : ℝ} {H : ℕ}
    (hCsrc : 1 ≤ Csrc)
    (hepsPos : 0 < epsCal) (hepsHi : epsCal ≤ 1 / 3)
    (hdetPos : 0 < deltaDet) (hdetHi : deltaDet ≤ 1)
    (hH : 4 ≤ H) (hetaPos : 0 < eta) (hetaHi : eta ≤ 1 / 2)
    (_hetaDrPos : 0 < etaDr) (hetaDrHi : etaDr ≤ min 1 (eta / 2))
    {Arad Bresp : ℝ} (_hArad : 0 ≤ Arad) (hBresp : 0 < Bresp)
    (hslack : 1 + 2 * Arad < initExpRhoMax d g * Bresp)
    (hsourceSmall : 24 * (Csrc * zetaG g) ^ 2 *
        (3 : ℝ) ^ (1 + 2 * Arad - initExpRhoMax d g * Bresp) ≤
      1 / 2 * eta ^ ((initExpQ d g : ℝ)⁻¹))
    (hsourceRow : 24 * (Csrc * zetaG g) ^ 2 /
        ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ 1)
    {P : Measure (CoeffSpace d)} {E : BlockMat d} {Psi : ℝ → ℝ}
    {Ksrc : ℝ} {Ssrc : CoeffSpace d → ℝ}
    (hP : IsProbabilityMeasure P)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi Ksrc Ssrc)
    {jStar M : ℤ} (hwin : IsCoupledWindow d (initExpQ d g : ℝ) Ksrc jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Psi Ksrc Csrc jStar M Y)
    (hYone : 1 ≤ ∫ a, Y a ∂P)
    (hYmean : ENNReal.ofReal (∫ a, Y a ∂P) ≤
      lqNorm P (initExpQ d g : ℝ) Y)
    (hYnorm : lqNorm P (initExpQ d g : ℝ) Y ≤ 2)
    {E0 : BlockMat d} {m0 q : Mat d} {s t : ℤ}
    (hE0symm : IsSymmetricBlockMat E0) (hE0pd : BlockPosDef E0)
    (hm0eq : m0 = canonicalMetric E0) (hqeq : q = roundedGrid jStar m0)
    (hjs : jStar ≤ s) (ht : t = s + (H : ℤ)) (hHt : (H : ℤ) < t)
    (hcells : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      adaptedCell q k ⊆ centeredCube d M)
    (hbelow : ∀ k : ℤ, k < jStar → ∀ v : ℤ, v = s ∨ v = t →
      ∀ z ∈ containedCenters q k v,
        adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hblocks : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (hmean : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k))
    (hfields : IsWindowedSourceFields P g Csrc E
      jStar m0 s t Y)
    {Cport : ℝ} (hCport : 1 ≤ Cport)
    (hportable : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) q jStar t ≤ ENNReal.ofReal Cport *
        portableProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) q jStar s t)
    (hts : BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q s))
    (hsSharp : BlockMatLoewnerLE (blockSharp (adaptedMean P q s))
      (adaptedMean P q s))
    (htSharp : BlockMatLoewnerLE (blockSharp (adaptedMean P q t))
      (adaptedMean P q t))
    (hdet : adaptedDetRoot P q s <
      (1 + deltaDet) * adaptedDetRoot P q t)
    (hcalLo : BlockMatLoewnerLE (blockScale (1 - epsCal) E0)
      (adaptedMean P q s))
    (hcalHi : BlockMatLoewnerLE (adaptedMean P q s)
      (blockScale (1 + epsCal) E0))
    (hdrift : linearDrift P (initExpRhoDr g) q jStar s +
      linearDrift P (initExpRhoDr g) q jStar t ≤ etaDr)
    {etaProfBar etaIn etaOut epsSt : ℝ}
    (_hetaProfPos : 0 < etaProfBar)
    (hetaProfCap : etaProfBar ≤ (2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta)
    (_hprofile : portableProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) q jStar s t ≤ ENNReal.ofReal etaOut)
    (hprofileScaled : ENNReal.ofReal Cport *
      portableProfile P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) q jStar s t ≤ ENNReal.ofReal epsSt)
    (hprofileMax : max (max etaIn etaOut) epsSt ≤ etaProfBar)
    (hkap : kappaRef E ≤ 6 * aspectRatio E)
    (hecc : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hbuf : jStar + ⌈Bresp * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s) :
    let hE0full : (toFullBlockMat E0).PosDef :=
      posDef_toFullBlockMat hE0symm hE0pd
    let hm0pd : m0.PosDef := by
      rw [hm0eq]
      exact ShortHop.posDef_canonicalMetric hE0full
    let hgrid : IsRoundedGrid jStar q :=
      isRoundedGrid_of_eq_roundedGrid_of_isCoupledWindow hwin hm0pd hqeq
    let hqpd := Recurrence.posDef_of_isRoundedGrid hgrid
    ∀ (hpreYoungMinus : ∀ Cresp, Cpre ≤ Cresp →
        ∀ (h0 : {h : Mat d // IsSkewMat h}) (p r : Vec d),
      let X := profilePrimalCenter P hqpd t
        (fun a ↦ a.subSkew h0 h0.property) p r
      let tau := profilePrimalResponseDefect P hqpd h0 h0.property s t p r
      let EJ := ∫ a, responseJ (adaptedDomain hqpd t)
        ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hqpd t)) p r ∂P
      let row := profilePrimalHattedEarlierRow P q h0 s X.1 X.2
      let weak := profilePrimalWeakQuantity P m0 hqpd t
        (fun a ↦ a.subSkew h0 h0.property) p r
      let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
        (fun i ↦ ∫ a, averageGradient (adaptedDomain hqpd t)
          ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hqpd t))
          (centeredResponseOptimizer (adaptedDomain hqpd t)
            (a.subSkew h0 h0.property) p r) i ∂P)
        (fun i ↦ ∫ a, averageFlux (adaptedDomain hqpd t)
          ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hqpd t))
          (centeredResponseOptimizer (adaptedDomain hqpd t)
            (a.subSkew h0 h0.property) p r) i ∂P)
      ENNReal.ofReal |Jtilde| ≤
        ENNReal.ofReal Cresp * ENNReal.ofReal (Real.sqrt tau) *
          (ENNReal.ofReal (Real.sqrt tau) + ENNReal.ofReal (Real.sqrt EJ) +
            row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal Cresp * ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
          ENNReal.ofReal (Real.sqrt EJ) *
            (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal Cresp * weak),
    ∀ (hpreYoungPlus : ∀ Cresp, Cpre ≤ Cresp →
        ∀ (h0 : {h : Mat d // IsSkewMat h}) (p r : Vec d),
      let X := profileAdjointCenter P hqpd t
        (fun a ↦ a.subSkew h0 h0.property) p r
      let tau := profileAdjointResponseDefect P hqpd h0 h0.property s t p r
      let EJ := ∫ a, responseJ (adaptedDomain hqpd t)
        ((a.subSkew h0 h0.property).transpose.coeffOn
          (adaptedDomain hqpd t)) p r ∂P
      let row := profileAdjointHattedEarlierRow P q h0 s X.1 X.2
      let weak := profileAdjointWeakQuantity P m0 hqpd t
        (fun a ↦ a.subSkew h0 h0.property) p r
      let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
        (fun i ↦ ∫ a, averageGradient (adaptedDomain hqpd t)
          ((a.subSkew h0 h0.property).transpose.coeffOn
            (adaptedDomain hqpd t))
          (centeredAdjointOptimizer (adaptedDomain hqpd t)
            (a.subSkew h0 h0.property) p r) i ∂P)
        (fun i ↦ ∫ a, averageFlux (adaptedDomain hqpd t)
          ((a.subSkew h0 h0.property).transpose.coeffOn
            (adaptedDomain hqpd t))
          (centeredAdjointOptimizer (adaptedDomain hqpd t)
            (a.subSkew h0 h0.property) p r) i ∂P)
      ENNReal.ofReal |Jtilde| ≤
        ENNReal.ofReal Cresp * ENNReal.ofReal (Real.sqrt tau) *
          (ENNReal.ofReal (Real.sqrt tau) + ENNReal.ofReal (Real.sqrt EJ) +
            row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal Cresp * ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
          ENNReal.ofReal (Real.sqrt EJ) *
            (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal Cresp * weak),
      let Cprof : ℝ := (exists_profile_response_constant hd).choose
      1 ≤ Cprof ∧
      let Cresp := max Cprof Cpre
      let cconst := (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹
      let GammaStar := 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1
      let cepsStar := Real.sqrt 2
      let betaStar := cepsStar * (1 + deltaDet) ^ ((d : ℝ) / 2)
      let chiTheta := Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2)
      let AStar := 2 * chiTheta
      let TStar := 2 * ((1 + deltaDet) ^ (d : ℝ) - 1) * chiTheta
      let LStar := 32 * GammaStar * cepsStar * betaStar *
        (1 + deltaDet) ^ ((d : ℝ) / 2) * chiTheta
      let KStar := Real.sqrt betaStar * (1 + deltaDet) ^ ((d : ℝ) / 4)
      let LenStar := 2 * Real.sqrt chiTheta
      let LambdaStar := Real.sqrt 5 * Real.sqrt chiTheta
      let Scen := 2 * ∑ r ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-(1 / 2 - initExpRhoMax d g) * (r : ℝ))
      let Scell := ∑ r ∈ Finset.Icc 1 H,
        (3 : ℝ) ^ (-(r : ℝ) / 2 +
          initExpA g * ((r : ℝ) - 1) / (initExpQ d g : ℝ))
      let Sav := ∑ r ∈ Finset.Icc 1 H,
        (3 : ℝ) ^ (-initExpA g * (r : ℝ) +
          initExpA g * ((r : ℝ) - 1) / (2 * (initExpQ d g : ℝ)))
      let UStar := (Scen + Scell) * eta ^ ((initExpQ d g : ℝ)⁻¹) +
        Sav * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹)
      let BStar := (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) * eta ^ ((2 : ℝ)⁻¹)
      let RStar := Cresp * KStar * LenStar * UStar +
        Cresp * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
          (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) +
        cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹)
      let omegaRsp := 2 * Cresp * (TStar + Real.sqrt (TStar * AStar) +
        Real.sqrt (TStar * LStar) +
        (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar)) +
        RStar ^ 2)
      ∀ (S SStar K : Mat d), S.PosDef → SStar.PosDef →
        toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K →
        0 ≤ omegaRsp ∧ sSup
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
  dsimp only
  intro hpreYoungMinus hpreYoungPlus
  let Cprof : ℝ := (exists_profile_response_constant hd).choose
  have hCprof := (exists_profile_response_constant hd).choose_spec.1
  have hprofileResponse := (exists_profile_response_constant hd).choose_spec.2
  refine ⟨hCprof, ?_⟩
  dsimp only
  intro S SStar K hS hStar hEtform
  letI : IsProbabilityMeasure P := hP
  haveI : NeZero d := ⟨by omega⟩
  have hm0pd' : m0.PosDef := by
    rw [hm0eq]
    exact posDef_canonMetric (posDef_toFullBlockMat hE0symm hE0pd)
  have hgrid' : IsRoundedGrid jStar q :=
    isRoundedGrid_of_eq_roundedGrid_of_isCoupledWindow hwin hm0pd' hqeq
  let hqpd' := Recurrence.posDef_of_isRoundedGrid hgrid'
  let Cresp : ℝ := max Cprof Cpre
  let TStar : ℝ := 2 * ((1 + deltaDet) ^ (d : ℝ) - 1) *
    (Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
  let AStar : ℝ := 2 *
    (Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
  let LStar : ℝ := 32 *
    (2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1) * Real.sqrt 2 *
    (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
    (1 + deltaDet) ^ ((d : ℝ) / 2) *
    (Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
  let RStar : ℝ := Cresp *
      (Real.sqrt (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
        (1 + deltaDet) ^ ((d : ℝ) / 4)) *
      (2 * Real.sqrt (Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2))) *
      (((2 * ∑ r ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-(1 / 2 - initExpRhoMax d g) * (r : ℝ))) +
        (∑ r ∈ Finset.Icc 1 H,
          (3 : ℝ) ^ (-(r : ℝ) / 2 +
            initExpA g * ((r : ℝ) - 1) / (initExpQ d g : ℝ)))) *
          eta ^ ((initExpQ d g : ℝ)⁻¹) +
        (∑ r ∈ Finset.Icc 1 H,
          (3 : ℝ) ^ (-initExpA g * (r : ℝ) +
            initExpA g * ((r : ℝ) - 1) / (2 * (initExpQ d g : ℝ)))) *
          eta ^ ((2 * (initExpQ d g : ℝ))⁻¹)) +
    Cresp *
      (Real.sqrt (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
        (1 + deltaDet) ^ ((d : ℝ) / 4)) * Real.sqrt 2 *
      (Real.sqrt 5 * Real.sqrt (Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2))) / (2 * initExpA g) *
      ((2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) * eta ^ ((2 : ℝ)⁻¹) +
        (3 : ℝ) ^ (-initExpA g * (H : ℝ))) +
    (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ *
      (Real.sqrt (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
        (1 + deltaDet) ^ ((d : ℝ) / 4)) *
      (2 * Real.sqrt (Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2))) *
      eta ^ ((initExpQ d g : ℝ)⁻¹)
  have hCresp : 1 ≤ Cresp :=
    (one_le_response_constant hCprof rfl).1
  have hTStar : 0 ≤ TStar :=
    (tStar_bounds (d := d) (deltaDet := deltaDet)
      (chiTheta := Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2)) (TStar := TStar)
      hdetPos.le hdetHi rfl rfl).1
  have hAStarTwo : 2 ≤ AStar :=
    (aStar_bounds (d := d) (deltaDet := deltaDet)
      (chiTheta := Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2)) (AStar := AStar)
      hdetPos.le hdetHi rfl rfl).1
  have hAStar : 0 ≤ AStar := le_trans (by norm_num) hAStarTwo
  have hLStar : 0 ≤ LStar :=
    (lStar_bounds (d := d) (deltaDet := deltaDet)
      (GammaStar := 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1)
      (cepsStar := Real.sqrt 2)
      (betaStar := Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2))
      (chiTheta := Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2)) (LStar := LStar)
      hdetPos.le hdetHi rfl rfl rfl rfl rfl).1
  have hEtPos : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
      (hblocks t (by omega) le_rfl).2
  have hEsPos : (toFullBlockMat (adaptedMean P q s)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q s)
      (hblocks s hjs (by omega)).2
  let rSym : Mat d := (2 : ℝ)⁻¹ • (K + Kᴴ)
  let hRsp : Mat d := responseSkew K
  let B : Mat d := S + rSymᴴ * SStar⁻¹ * rSym
  let m : Mat d := matGeomMean B SStar
  let g0 : Mat d := canonicalShear E0
  let G0 : FullBlockMat d := fullBlockShear g0
  let M0 : FullBlockMat d := Matrix.fromBlocks m0 0 0 m0⁻¹
  let Ehat : FullBlockMat d :=
    G0ᴴ * toFullBlockMat (adaptedMean P q t) * G0
  let Eshat : FullBlockMat d :=
    G0ᴴ * toFullBlockMat (adaptedMean P q s) * G0
  let ceps : ℝ := Real.sqrt ((1 + epsCal) / (1 - epsCal))
  let rho : ℝ := canonDetRatio (toFullBlockMat (adaptedMean P q s))
    (toFullBlockMat (adaptedMean P q t))
  let beta : ℝ := ceps * Real.sqrt (rho ^ d)
  have hlow : (1 - epsCal) • toFullBlockMat E0 ≤
      toFullBlockMat (adaptedMean P q s) := by
    simpa only [toFullBlockMat_blockScale] using
      (le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockScale _ hE0symm)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hcalLo)
  have hhigh : toFullBlockMat (adaptedMean P q s) ≤
      (1 + epsCal) • toFullBlockMat E0 := by
    simpa only [toFullBlockMat_blockScale] using
      (le_of_blockMatLoewnerLE (Recurrence.isSymmetricBlockMat_adaptedMean P q s)
        (isSymmetricBlockMat_blockScale _ hE0symm) hcalHi)
  have hsSharpFull : fullBlockSharp
      (toFullBlockMat (adaptedMean P q s)) ≤
      toFullBlockMat (adaptedMean P q s) := by
    simpa only [toFullBlockMat_blockSharp] using
      (le_of_blockMatLoewnerLE
        (isSymmetricBlockMat_blockSharp
          (Recurrence.isSymmetricBlockMat_adaptedMean P q s)
          (hblocks s hjs (by omega)).2)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hsSharp)
  have htSharpFull : fullBlockSharp
      (toFullBlockMat (adaptedMean P q t)) ≤
      toFullBlockMat (adaptedMean P q t) := by
    simpa only [toFullBlockMat_blockSharp] using
      (le_of_blockMatLoewnerLE
        (isSymmetricBlockMat_blockSharp
          (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
          (hblocks t (by omega) le_rfl).2)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t) htSharp)
  have hratio : rho < 1 + deltaDet := by
    have hrootT : 0 < adaptedDetRoot P q t := ShortHop.detRoot_pos hEtPos
    rw [show rho = adaptedDetRoot P q s / adaptedDetRoot P q t by
      exact canonDetRatio_eq_adaptedDetRoot_div rfl rfl hEsPos hEtPos]
    exact (div_lt_iff₀ hrootT).2 hdet
  have hkappa : 1 ≤ blockImbalance (adaptedMean P q s) := by
    exact Persistence.one_le_blockImbalance_adaptedMean hgrid' s
      (hblocks s hjs (by omega)).1
  have hcalibrationAt (e : Vec d) (he : e ⬝ᵥ e = 1) :=
    response_load_calibration hd
      (posDef_toFullBlockMat hE0symm hE0pd) hEsPos hEtPos
      (le_of_blockMatLoewnerLE (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hts)
      hsSharpFull htSharpFull hepsPos.le (by linarith only [hepsHi])
      hlow hhigh rfl rfl rfl hS hStar hEtform rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl
      he rfl rfl
  have homega : 0 ≤ 2 * Cresp *
      (TStar + Real.sqrt (TStar * AStar) + Real.sqrt (TStar * LStar) +
        (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar)) +
        RStar ^ 2) :=
    omegaRsp_nonneg (le_trans zero_le_one hCresp) hTStar hAStar
      (Real.rpow_nonneg (by norm_num) _) rfl
  have hg0 : IsSkewMat (canonicalShear E0) := by
    rw [IsSkewMat, canonicalShear]
    exact (canonFactor_spec
      (posDef_toFullBlockMat hE0symm hE0pd)).2.1
  let h0 : {h : Mat d // IsSkewMat h} := ⟨canonicalShear E0, hg0⟩
  let pLoad : Vec d → Vec d := fun e ↦ centeredResponseLoadP S SStar K e
  let rLoad : Vec d → Vec d := fun e ↦ centeredResponseLoadQ S SStar K e
  let rMinus : Vec d → Vec d := fun e ↦
    rLoad e + (canonicalShear E0 - responseSkew K) *ᵥ pLoad e
  let rPlus : Vec d → Vec d := fun e ↦
    rLoad e + (responseSkew K - canonicalShear E0) *ᵥ pLoad e
  let tauMinus : Vec d → ℝ := fun e ↦
    profilePrimalResponseDefect P hqpd' h0 h0.property s t (pLoad e) (rMinus e)
  let tauPlus : Vec d → ℝ := fun e ↦
    profileAdjointResponseDefect P hqpd' h0 h0.property s t (pLoad e) (rPlus e)
  let EJMinus : Vec d → ℝ := fun e ↦ ∫ a,
    responseJ (adaptedDomain hqpd' t)
      ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hqpd' t))
      (pLoad e) (rMinus e) ∂P
  let EJPlus : Vec d → ℝ := fun e ↦ ∫ a,
    responseJ (adaptedDomain hqpd' t)
      ((a.subSkew h0 h0.property).transpose.coeffOn (adaptedDomain hqpd' t))
      (pLoad e) (rPlus e) ∂P
  let centerMinus : Vec d → Vec d × Vec d := fun e ↦
    profilePrimalCenter P hqpd' t (fun a ↦ a.subSkew h0 h0.property)
      (pLoad e) (rMinus e)
  let centerPlus : Vec d → Vec d × Vec d := fun e ↦
    profileAdjointCenter P hqpd' t (fun a ↦ a.subSkew h0 h0.property)
      (pLoad e) (rPlus e)
  let rowMinus : Vec d → ℝ≥0∞ := fun e ↦
    profilePrimalHattedEarlierRow P q h0 s (centerMinus e).1 (centerMinus e).2
  let rowPlus : Vec d → ℝ≥0∞ := fun e ↦
    profileAdjointHattedEarlierRow P q h0 s (centerPlus e).1 (centerPlus e).2
  let weakMinus : Vec d → ℝ≥0∞ := fun e ↦
    profilePrimalWeakQuantity P m0 hqpd' t
      (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rMinus e)
  let weakPlus : Vec d → ℝ≥0∞ := fun e ↦
    profileAdjointWeakQuantity P m0 hqpd' t
      (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rPlus e)
  have hQgt : 2 < initExpQ d g := by
    have hQ12 := twelve_le_initExpQ hd hg
    omega
  have hprofileAt (e : Vec d) := hprofileResponse
    (initExpQ d g) initExpQ_even hQgt P hP g hg E Psi Ksrc Ssrc Csrc
    hstat hunit hdag hCsrc jStar M hwin Y hY hYone hYmean hYnorm
    (initExpRhoMax d g) (lt_initExpRhoMax hd hg)
    (initExpRhoMax_lt_half_add hd hg) (initExpA_le_mul_sub hd hg)
    E0 m0 q hE0symm hE0pd hm0eq hqeq hgrid' s t H hjs ht hH hHt
    hcells hbelow hblocks hmean hfields Cport hCport hportable h0
    (pLoad e) (rMinus e) (pLoad e) (rPlus e)
  have hrhoNonneg : 0 ≤ rho := by
    dsimp only [rho]
    exact canonDetRatio_nonneg
      (div_nonneg hEsPos.det_pos.le hEtPos.det_pos.le)
  obtain ⟨hrhoOne, ⟨_, hdetLoss⟩, _, _⟩ :=
    canonDeterminantLoss_canonDetRatio hd hEsPos hEtPos
      (le_of_blockMatLoewnerLE
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hts)
  have hhatTS : Ehat ≤ Eshat := by
    dsimp only [Ehat, Eshat, G0]
    exact conj_le_conj (fullBlockShear (canonicalShear E0))
      (le_of_blockMatLoewnerLE
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hts)
  have hhatLoss : Eshat ≤ rho ^ d • Ehat := by
    dsimp only [Ehat, Eshat, G0]
    simpa only [conj_smul] using
      (conj_le_conj (fullBlockShear (canonicalShear E0)) hdetLoss)
  have hEhatPos : Ehat.PosDef := by
    dsimp only [Ehat, G0]
    exact posDef_conj hEtPos (isUnit_fullBlockShear (canonicalShear E0))
  have hrhoOne' : 1 ≤ rho := by simpa only [rho] using hrhoOne
  have hrhoPowOne : 1 ≤ rho ^ d := one_le_pow₀ hrhoOne'
  have hR0 : 0 ≤ 1 + deltaDet := by linarith only [hdetPos]
  have hRpowOne : 1 ≤ (1 + deltaDet) ^ d := by
    exact one_le_pow₀ (by linarith only [hdetPos])
  have hrhoPowNat : rho ^ d ≤ (1 + deltaDet) ^ d :=
    pow_le_pow_left₀ hrhoNonneg (le_of_lt hratio) d
  have hrhoPow : rho ^ d ≤ (1 + deltaDet) ^ (d : ℝ) := by
    simpa only [Real.rpow_natCast] using hrhoPowNat
  have hthetaRootAt (e : Vec d) (he : e ⬝ᵥ e = 1) :
      Real.sqrt (relSize B SStar) ≤
        (Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
          Real.sqrt (blockImbalance (adaptedMean P q s)) := by
    obtain ⟨_, hcomp, htheta, _, _, _, _, _⟩ := hcalibrationAt e he
    have hcompare : blockImbalance (adaptedMean P q t) ≤
        (1 + deltaDet) ^ (d : ℝ) * blockImbalance (adaptedMean P q s) :=
      hcomp.1.trans (mul_le_mul_of_nonneg_right hrhoPow
        (canonImbalance_nonneg _))
    exact sqrt_theta_le_chi hR0 htheta.2.1 hcompare rfl
  have henergyAt (e : Vec d) (he : e ⬝ᵥ e = 1) :=
    shifted_annealed_response_energies_eq_and_nonneg hqpd'
      (hblocks t (by omega) le_rfl).1 hS hStar hg0 hEtform
      (Ehat := Ehat) rfl e he
  have hPi : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hsourceCap : kappaRef E * boundaryConst Csrc g m0 ^ 2 * 2 ^ 2 /
      ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) ≤ 1 :=
    source_row_bound_cap hd hg hPi hBresp hslack hsourceRow
      hkap hecc hbuf
  have hdriftS : linearDrift P (initExpRhoDr g) q jStar s ≤ 1 := by
    have hdriftT0 := Bridge.linearDrift_nonneg (b := jStar) (T := t)
      hstat hgrid' le_rfl (by omega)
      (fun k hk hkt ↦ (hblocks k hk hkt).1) (initExpRhoDr g)
    calc
      linearDrift P (initExpRhoDr g) q jStar s ≤
          linearDrift P (initExpRhoDr g) q jStar s +
            linearDrift P (initExpRhoDr g) q jStar t :=
        le_add_of_nonneg_right hdriftT0
      _ ≤ etaDr := hdrift
      _ ≤ 1 := hetaDrHi.trans (min_le_left _ _)
  have hGamma0 : 0 ≤ profileRowGamma P (initExpRhoDr g) q Csrc g E
      jStar m0 s :=
    profileRowGamma_nonneg hstat hgrid' hjs
      (fun k hk hks ↦ (hblocks k hk (by omega)).1) hg.2 E m0
  have hGamma : profileRowGamma P (initExpRhoDr g) q Csrc g E
      jStar m0 s ≤ 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1 :=
    profile_row_gamma_le rfl hdriftS hsourceCap
  have hceps0 : 0 ≤ ceps := by
    dsimp only [ceps]
    positivity
  have hcepsBound : ceps ≤ Real.sqrt 2 := by
    exact sqrt_calibration_le_sqrt_two hepsHi
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbetaBound : beta ≤
      Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2) := by
    have hroot : Real.sqrt (rho ^ d) ≤
        (1 + deltaDet) ^ ((d : ℝ) / 2) := by
      simpa only [Real.sqrt_one, mul_one] using
        (sqrt_comparison_le (d := d) hR0
          (y := (1 : ℝ)) (by simpa only [mul_one] using hrhoPow))
    exact mul_le_mul hcepsBound hroot (Real.sqrt_nonneg _)
      (by positivity)
  have hhistory := history_profile_smallness
    (Nat.zero_lt_of_lt hQgt) hetaPos.le hportable hprofileScaled
      hprofileMax hetaProfCap
  have hcenteredCap : centeredHistory P (initExpQ d g : ℝ)
      (initExpRhoMax d g) q jStar t ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta) := by
    apply (show centeredHistory P (initExpQ d g : ℝ)
      (initExpRhoMax d g) q jStar t ≤
        portableHistory P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) q jStar t by
      rw [portableHistory]
      exact le_self_add).trans
    exact hhistory.1
  have hnonlinearCap : nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(initExpQ d g : ℤ)) * eta) := by
    apply (show nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ≤
        portableHistory P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) q jStar t by
      rw [portableHistory]
      exact le_add_self).trans
    exact hhistory.1
  have hcenteredEta : centeredHistory P (initExpQ d g : ℝ)
      (initExpRhoMax d g) q jStar t ≤ ENNReal.ofReal eta :=
    (show centeredHistory P (initExpQ d g : ℝ)
      (initExpRhoMax d g) q jStar t ≤
        portableHistory P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) q jStar t by
      rw [portableHistory]
      exact le_self_add).trans hhistory.2
  have hnonlinearEta : nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ≤ ENNReal.ofReal eta :=
    (show nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ≤
        portableHistory P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) q jStar t by
      rw [portableHistory]
      exact le_add_self).trans hhistory.2
  have hcenteredRoot : centeredHistory P (initExpQ d g : ℝ)
      (initExpRhoMax d g) q jStar t ^ (initExpQ d g : ℝ)⁻¹ ≤
        ENNReal.ofReal (eta ^ (initExpQ d g : ℝ)⁻¹) :=
    history_root_le_of_cap hetaPos.le
      (inv_nonneg.mpr (Nat.cast_nonneg _)) hcenteredEta
  have hnonlinearRoot : nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ^ (initExpQ d g : ℝ)⁻¹ ≤
        ENNReal.ofReal (eta ^ (initExpQ d g : ℝ)⁻¹) :=
    history_root_le_of_cap hetaPos.le
      (inv_nonneg.mpr (Nat.cast_nonneg _)) hnonlinearEta
  have hnonlinearHalf : nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ^ (2 * (initExpQ d g : ℝ))⁻¹ ≤
        ENNReal.ofReal (eta ^ (2 * (initExpQ d g : ℝ))⁻¹) :=
    history_root_le_of_cap hetaPos.le
      (inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      hnonlinearEta
  have hsourceReal := source_maximum_bound hd hg hPi hslack hsourceSmall
    hkap hecc hbuf (by omega : s < t)
  have hdriftS0 := Bridge.linearDrift_nonneg (b := jStar) (T := s)
    hstat hgrid' le_rfl hjs
    (fun k hk hks ↦ (hblocks k hk (by omega)).1) (initExpRhoDr g)
  have hdriftT : linearDrift P (initExpRhoDr g) q jStar t ≤ eta / 2 := by
    calc
      linearDrift P (initExpRhoDr g) q jStar t ≤ etaDr := by
        linarith only [hdrift, hdriftS0]
      _ ≤ eta / 2 := hetaDrHi.trans (min_le_right _ _)
  refine ⟨homega, ?_⟩
  apply centered_response_sup_le_of_compact_pre_young
    (adaptedDomain hqpd' t)
    (le_trans zero_le_one hCresp) (Real.rpow_nonneg (by norm_num) _)
    hTStar hAStar hLStar hkappa rfl tauMinus tauPlus EJMinus EJPlus
    rowMinus rowPlus weakMinus weakPlus
  · intro e _he
    apply shifted_primal_carrier_le hqpd'
      (hblocks t (by omega) le_rfl).1 hg0 (pLoad e) (rLoad e)
    simpa only [h0, pLoad, rLoad, rMinus, tauMinus, EJMinus, centerMinus,
      rowMinus, weakMinus] using
      (hpreYoungMinus Cresp (le_max_right _ _) h0 (pLoad e) (rMinus e))
  · intro e _he
    apply shifted_adjoint_carrier_le hqpd'
      (hblocks t (by omega) le_rfl).1 hg0 (pLoad e) (rLoad e)
    simpa only [h0, pLoad, rLoad, rPlus, tauPlus, EJPlus, centerPlus,
      rowPlus, weakPlus] using
      (hpreYoungPlus Cresp (le_max_right _ _) h0 (pLoad e) (rPlus e))
  · intro e he
    rcases hprofileAt e with
      ⟨_, _, _, _, _, _, _, _, hdefectIdentity, _, _, _, _⟩
    obtain ⟨_, _, _, _, hloadSq, _, _, _⟩ := hcalibrationAt e he
    have hload : Sum.elim (-(pLoad e)) (rMinus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (-(pLoad e)) (rMinus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rMinus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.1
    have hraw := (defect_bounds (Ethat := Ehat) (Eshat := Eshat)
      hEhatPos.posSemidef hhatTS hrhoPowOne hhatLoss
      (Sum.elim (-(pLoad e)) (rMinus e)) hload).2
    have hraw' : tauMinus e ≤
        2 * (rho ^ d - 1) * Real.sqrt (relSize B SStar) := by
      change profilePrimalResponseDefect P hqpd' h0 h0.property s t
        (pLoad e) (rMinus e) ≤ _
      rw [hdefectIdentity.1]
      simpa only [tauMinus, h0, pLoad, rMinus, Ehat, Eshat, G0, g0,
        profileRecenteredMean, toFullBlockMat_blockMatMul,
        toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
        Recurrence.toFullBlockMat_blockSub,
        blockVecDot_blockMatVecMul_eq_dotProduct, Matrix.mul_assoc,
        Matrix.sub_mulVec, dotProduct_sub, one_div,
        to_full_block_vec_pair] using hraw
    obtain ⟨_, hcomp, htheta, _, _, _, _, _⟩ := hcalibrationAt e he
    have hcompare : blockImbalance (adaptedMean P q t) ≤
        (1 + deltaDet) ^ (d : ℝ) * blockImbalance (adaptedMean P q s) := by
      exact hcomp.1.trans (mul_le_mul_of_nonneg_right hrhoPow
        (canonImbalance_nonneg _))
    have hthetaRoot : Real.sqrt (relSize B SStar) ≤
        (Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
          Real.sqrt (blockImbalance (adaptedMean P q s)) :=
      sqrt_theta_le_chi hR0 htheta.2.1 hcompare rfl
    exact defect_le_t_star hrhoPow
      (by simpa only [Real.rpow_natCast] using hRpowOne)
      hthetaRoot hraw' rfl
  · intro e he
    obtain ⟨_, hcomp, htheta, _, hloadSq, _, _, _⟩ := hcalibrationAt e he
    have hload : Sum.elim (pLoad e) (rPlus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (pLoad e) (rPlus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rPlus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.2
    have hraw := (defect_bounds (Ethat := Ehat) (Eshat := Eshat)
      hEhatPos.posSemidef hhatTS hrhoPowOne hhatLoss
      (Sum.elim (pLoad e) (rPlus e)) hload).2
    have hraw' : tauPlus e ≤
        2 * (rho ^ d - 1) * Real.sqrt (relSize B SStar) := by
      change profileAdjointResponseDefect P hqpd' h0 h0.property s t
        (pLoad e) (rPlus e) ≤ _
      rw [profile_adjoint_response_defect_eq_recentered_quadratic hqpd'
        hg0 (hblocks s hjs (by omega)).1
        (hblocks t (by omega) le_rfl).1]
      simpa only [tauPlus, h0, pLoad, rPlus, Ehat, Eshat, G0, g0,
        profileRecenteredMean, toFullBlockMat_blockMatMul,
        toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
        blockVecDot_blockMatVecMul_eq_dotProduct, Matrix.mul_assoc,
        one_div,
        to_full_block_vec_pair] using hraw
    have hcompare : blockImbalance (adaptedMean P q t) ≤
        (1 + deltaDet) ^ (d : ℝ) * blockImbalance (adaptedMean P q s) := by
      exact hcomp.1.trans (mul_le_mul_of_nonneg_right hrhoPow
        (canonImbalance_nonneg _))
    have hthetaRoot : Real.sqrt (relSize B SStar) ≤
        (Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
          Real.sqrt (blockImbalance (adaptedMean P q s)) :=
      sqrt_theta_le_chi hR0 htheta.2.1 hcompare rfl
    exact defect_le_t_star hrhoPow
      (by simpa only [Real.rpow_natCast] using hRpowOne)
      hthetaRoot hraw' rfl
  · intro e he
    rcases henergyAt e he with ⟨⟨hid, hnonneg⟩, _⟩
    obtain ⟨_, _, _, _, hloadSq, _, _, _⟩ := hcalibrationAt e he
    have hid' : EJMinus e = (2 : ℝ)⁻¹ *
        (Sum.elim (-(pLoad e)) (rMinus e) ⬝ᵥ Ehat *ᵥ
          Sum.elim (-(pLoad e)) (rMinus e)) - 1 := by
      simpa only [EJMinus, pLoad, rLoad, rMinus, h0, one_div] using hid
    have hnonneg' : 0 ≤ EJMinus e := by
      simpa only [EJMinus, pLoad, rLoad, rMinus, h0] using hnonneg
    have hload : Sum.elim (-(pLoad e)) (rMinus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (-(pLoad e)) (rMinus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rMinus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.1
    have hchain := energy_chain hnonneg' hid' hload
    change EJMinus e ≤ AStar *
      Real.sqrt (blockImbalance (adaptedMean P q s))
    exact energy_le_a_star (hthetaRootAt e he)
      (hchain.2.1.trans hchain.2.2) rfl
  · intro e he
    rcases henergyAt e he with ⟨_, ⟨hid, hnonneg⟩⟩
    obtain ⟨_, _, _, _, hloadSq, _, _, _⟩ := hcalibrationAt e he
    have hid' : EJPlus e = (2 : ℝ)⁻¹ *
        (Sum.elim (pLoad e) (rPlus e) ⬝ᵥ Ehat *ᵥ
          Sum.elim (pLoad e) (rPlus e)) - 1 := by
      simpa only [EJPlus, pLoad, rLoad, rPlus, h0, one_div] using hid
    have hnonneg' : 0 ≤ EJPlus e := by
      simpa only [EJPlus, pLoad, rLoad, rPlus, h0] using hnonneg
    have hload : Sum.elim (pLoad e) (rPlus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (pLoad e) (rPlus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rPlus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.2
    have hchain := energy_chain hnonneg' hid' hload
    change EJPlus e ≤ AStar *
      Real.sqrt (blockImbalance (adaptedMean P q s))
    exact energy_le_a_star (hthetaRootAt e he)
      (hchain.2.1.trans hchain.2.2) rfl
  · intro e he
    rcases hprofileAt e with
      ⟨_, _, _, _, _, _, _, _, _, _, _, hrows, _⟩
    obtain ⟨_, hcomp, _, _, hloadSq, hterminal, hearlier, _⟩ :=
      hcalibrationAt e he
    have hbetaPos : 0 < beta := by
      have hdetRatio : 0 < rho := by
        dsimp only [rho, canonDetRatio]
        exact Real.rpow_pos_of_pos
          (div_pos hEsPos.det_pos hEtPos.det_pos) _
      dsimp only [beta, ceps]
      exact mul_pos (Real.sqrt_pos.mpr (div_pos
        (by linarith only [hepsPos]) (by linarith only [hepsHi])))
        (Real.sqrt_pos.mpr (pow_pos hdetRatio d))
    have hkappaTPos : 0 < blockImbalance (adaptedMean P q t) :=
      lt_of_lt_of_le one_pos
        (Persistence.one_le_blockImbalance_adaptedMean hgrid' t
          (hblocks t (by omega) le_rfl).1)
    have hload : Sum.elim (-(pLoad e)) (rMinus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (-(pLoad e)) (rMinus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rMinus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.1
    have hcenterMetric : Sum.elim (centerMinus e).1 (centerMinus e).2 ⬝ᵥ
        M0 *ᵥ Sum.elim (centerMinus e).1 (centerMinus e).2 ≤
          8 * beta * (Real.sqrt (blockImbalance (adaptedMean P q t)) + 1) *
            Real.sqrt (relSize B SStar) := by
      apply primal_center_metric_le_of_calibration hqpd'
        (hblocks t (by omega) le_rfl).1 hg0 (pLoad e) (rMinus e)
        (M0 := M0) (Ehat := Ehat) (beta := beta)
        (kappa := blockImbalance (adaptedMean P q t))
        (theta := relSize B SStar) hm0pd' rfl
      · simp only [Ehat, G0, g0, toFullBlockMat_skewBlockCongr,
          Matrix.mul_assoc]
      · exact hEhatPos
      · exact hbetaPos
      · exact hkappaTPos
      · simpa only [beta, M0, Ehat, G0, g0, hm0eq,
          canonicalMetric, canonicalShear, blockImbalance] using hterminal.1
      · simpa only [beta, M0, Ehat, G0, g0, hm0eq,
          canonicalMetric, canonicalShear, blockImbalance] using hterminal.2
      · exact hload
    have hquad : profileQuadraticLoad
        (profileRecenteredMean P q (canonicalShear E0) s)
          (centerMinus e).1 (centerMinus e).2 ≤
        ceps * Real.sqrt (blockImbalance (adaptedMean P q s)) *
          (8 * beta * (Real.sqrt (blockImbalance (adaptedMean P q t)) + 1) *
            Real.sqrt (relSize B SStar)) := by
      apply profile_quadratic_load_le_row_load (M0 := M0) rfl
        (mul_nonneg hceps0 (Real.sqrt_nonneg _))
      · simpa only [profileRecenteredMean, toFullBlockMat_blockMatMul,
          toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
          Eshat, G0, g0, M0, ceps, hm0eq, canonicalMetric,
          canonicalShear, blockImbalance, Matrix.mul_assoc] using hearlier
      · exact hcenterMetric
    have hprofileRow : rowMinus e ≤ ENNReal.ofReal
        (2 * profileRowGamma P (initExpRhoDr g) q Csrc g E jStar m0 s *
          profileQuadraticLoad
            (profileRecenteredMean P q (canonicalShear E0) s)
            (centerMinus e).1 (centerMinus e).2) := by
      simpa only [rowMinus, centerMinus, h0] using hrows.1.2
    have hcompare : blockImbalance (adaptedMean P q t) ≤
        (1 + deltaDet) ^ (d : ℝ) * blockImbalance (adaptedMean P q s) :=
      hcomp.1.trans (mul_le_mul_of_nonneg_right hrhoPow
        (canonImbalance_nonneg _))
    have hquad' : profileQuadraticLoad
        (profileRecenteredMean P q (canonicalShear E0) s)
          (centerMinus e).1 (centerMinus e).2 ≤
        8 * ceps * beta * Real.sqrt (blockImbalance (adaptedMean P q s)) *
          (Real.sqrt (blockImbalance (adaptedMean P q t)) + 1) *
          Real.sqrt (relSize B SStar) := by
      calc
        profileQuadraticLoad
            (profileRecenteredMean P q (canonicalShear E0) s)
              (centerMinus e).1 (centerMinus e).2 ≤
            ceps * Real.sqrt (blockImbalance (adaptedMean P q s)) *
              (8 * beta *
                (Real.sqrt (blockImbalance (adaptedMean P q t)) + 1) *
                Real.sqrt (relSize B SStar)) := hquad
        _ = _ := by ring
    exact hatted_row_le_l_star_of_profile
      (Rhalf := (1 + deltaDet) ^ ((d : ℝ) / 2))
      (chi := Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
      hGamma0 hceps0 hbeta0
      (Real.one_le_rpow (by linarith only [hdetPos]) (by positivity))
      hkappa hGamma hcepsBound hbetaBound
      (sqrt_comparison_le hR0 hcompare) (hthetaRootAt e he)
      hprofileRow hquad' rfl
  · intro e he
    rcases hprofileAt e with
      ⟨_, _, _, _, _, _, _, _, _, _, _, hrows, _⟩
    obtain ⟨_, hcomp, _, _, hloadSq, hterminal, hearlier, _⟩ :=
      hcalibrationAt e he
    have hbetaPos : 0 < beta := by
      have hdetRatio : 0 < rho := by
        dsimp only [rho, canonDetRatio]
        exact Real.rpow_pos_of_pos
          (div_pos hEsPos.det_pos hEtPos.det_pos) _
      dsimp only [beta, ceps]
      exact mul_pos (Real.sqrt_pos.mpr (div_pos
        (by linarith only [hepsPos]) (by linarith only [hepsHi])))
        (Real.sqrt_pos.mpr (pow_pos hdetRatio d))
    have hkappaTPos : 0 < blockImbalance (adaptedMean P q t) :=
      lt_of_lt_of_le one_pos
        (Persistence.one_le_blockImbalance_adaptedMean hgrid' t
          (hblocks t (by omega) le_rfl).1)
    have hload : Sum.elim (pLoad e) (rPlus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (pLoad e) (rPlus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rPlus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.2
    have hcenterMetric : Sum.elim (centerPlus e).1 (centerPlus e).2 ⬝ᵥ
        M0 *ᵥ Sum.elim (centerPlus e).1 (centerPlus e).2 ≤
          8 * beta * (Real.sqrt (blockImbalance (adaptedMean P q t)) + 1) *
            Real.sqrt (relSize B SStar) := by
      apply adjoint_center_metric_le_of_calibration hqpd'
        (hblocks t (by omega) le_rfl).1 hg0 (pLoad e) (rPlus e)
        (M0 := M0) (Ehat := Ehat) (beta := beta)
        (kappa := blockImbalance (adaptedMean P q t))
        (theta := relSize B SStar) hm0pd' rfl
      · simp only [Ehat, G0, g0, toFullBlockMat_skewBlockCongr,
          Matrix.mul_assoc]
      · exact hEhatPos
      · exact hbetaPos
      · exact hkappaTPos
      · simpa only [beta, M0, Ehat, G0, g0, hm0eq,
          canonicalMetric, canonicalShear, blockImbalance] using hterminal.1
      · simpa only [beta, M0, Ehat, G0, g0, hm0eq,
          canonicalMetric, canonicalShear, blockImbalance] using hterminal.2
      · exact hload
    have hquadBase : profileQuadraticLoad
        (profileRecenteredMean P q (canonicalShear E0) s)
          (centerPlus e).1 (centerPlus e).2 ≤
        ceps * Real.sqrt (blockImbalance (adaptedMean P q s)) *
          (8 * beta * (Real.sqrt (blockImbalance (adaptedMean P q t)) + 1) *
            Real.sqrt (relSize B SStar)) := by
      apply adjoint_center_quadratic_load_le hqpd'
        (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rPlus e)
        (M0 := M0) rfl (mul_nonneg hceps0 (Real.sqrt_nonneg _))
      · simpa only [profileRecenteredMean, toFullBlockMat_blockMatMul,
          toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
          Eshat, G0, g0, M0, ceps, hm0eq, canonicalMetric,
          canonicalShear, blockImbalance, Matrix.mul_assoc] using hearlier
      · simpa only [centerPlus] using hcenterMetric
    have hquad : profileQuadraticLoad
        (profileRecenteredAdjointMean P q (canonicalShear E0) s)
          (centerPlus e).1 (centerPlus e).2 ≤
        8 * ceps * beta * Real.sqrt (blockImbalance (adaptedMean P q s)) *
          (Real.sqrt (blockImbalance (adaptedMean P q t)) + 1) *
          Real.sqrt (relSize B SStar) := by
      rw [← profileHattedAdjointBlock_adaptedMean,
        hatted_adjoint_quadratic_load_eq,
        profileHattedBlock_adaptedMean]
      calc
        profileQuadraticLoad
            (profileRecenteredMean P q (canonicalShear E0) s)
              (centerPlus e).1 (centerPlus e).2 ≤ _ := hquadBase
        _ = _ := by ring
    have hprofileRow : rowPlus e ≤ ENNReal.ofReal
        (2 * profileRowGamma P (initExpRhoDr g) q Csrc g E jStar m0 s *
          profileQuadraticLoad
            (profileRecenteredAdjointMean P q (canonicalShear E0) s)
            (centerPlus e).1 (centerPlus e).2) := by
      simpa only [rowPlus, centerPlus, h0] using hrows.2.2
    have hcompare : blockImbalance (adaptedMean P q t) ≤
        (1 + deltaDet) ^ (d : ℝ) * blockImbalance (adaptedMean P q s) :=
      hcomp.1.trans (mul_le_mul_of_nonneg_right hrhoPow
        (canonImbalance_nonneg _))
    exact hatted_row_le_l_star_of_profile
      (Rhalf := (1 + deltaDet) ^ ((d : ℝ) / 2))
      (chi := Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2))
      hGamma0 hceps0 hbeta0
      (Real.one_le_rpow (by linarith only [hdetPos]) (by positivity))
      hkappa hGamma hcepsBound hbetaBound
      (sqrt_comparison_le hR0 hcompare) (hthetaRootAt e he)
      hprofileRow hquad rfl
  · intro e he
    rcases hprofileAt e with
      ⟨hsource, hmaxGroup, hcell, hav, henergy, hN, _, hcenter,
        _, _, _, _, _⟩
    obtain ⟨_, hcomp, htheta, _, hloadSq, hterminal, _, _⟩ :=
      hcalibrationAt e he
    let Fhat := profileRecenteredMean P q (canonicalShear E0) t
    let Kfac := diagonalWeakMetricFactor m0 Fhat
    let LenM := diagonalWeakLoadMinus Fhat (pLoad e) (rMinus e)
    let LamM := profileEnergyLoad LenM (pLoad e) (rMinus e)
    have hFhat := profileRecenteredMean_symm_posDef
      (g := canonicalShear E0) (hblocks t (by omega) le_rfl).2
    have hK0 : 0 ≤ Kfac := diagonalWeakMetricFactor_nonneg m0 Fhat
    have hLen0 : 0 ≤ LenM :=
      diagonalWeakLoadMinus_nonneg Fhat (pLoad e) (rMinus e)
    have hLam0 : 0 ≤ LamM :=
      profileEnergyLoad_nonneg LenM (pLoad e) (rMinus e)
    have hKsq : Kfac ^ 2 = relSize Ehat M0 := by
      rw [sq_diagonalWeakMetricFactor hm0pd' hFhat.1,
        blockSize_eq_relSize hFhat.1
          (isSymmetricBlockMat_diagonalMetric hm0pd')
          (blockPosDef_diagonalMetric hm0pd')
          (posDef_toFullBlockMat hFhat.1 hFhat.2).posSemidef]
      simp only [profileRecenteredMean, toFullBlockMat_blockMatMul,
        toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
        toFullBlockMat_blockDiag, Ehat, G0, g0, M0, hm0eq,
        canonicalMetric, Matrix.mul_assoc]
    have hKraw : Kfac ≤ Real.sqrt beta *
        Real.sqrt (Real.sqrt (blockImbalance (adaptedMean P q t))) :=
      profile_factor_le hm0pd' rfl hEhatPos.posSemidef hK0 hKsq hbeta0
        (by simpa only [beta, M0, Ehat, G0, g0, hm0eq,
          canonicalMetric, canonicalShear, blockImbalance] using hterminal.2)
    have hload : Sum.elim (-(pLoad e)) (rMinus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (-(pLoad e)) (rMinus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rMinus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.1
    have hLenSq : LenM ^ 2 ≤ 4 * Real.sqrt (relSize B SStar) := by
      rw [sq_diagonalWeakLoadMinus hFhat.1 hFhat.2,
        blockVecDot_blockMatVecMul_eq_dotProduct]
      simpa only [LenM, Fhat, Ehat, G0, g0, profileRecenteredMean,
        toFullBlockMat_blockMatMul, toFullBlockMat_blockMatTranspose_conj,
        toFullBlockMat_blockG, Matrix.mul_assoc,
        to_full_block_vec_pair] using hload
    have hLenRaw : LenM ≤
        2 * Real.sqrt (Real.sqrt (relSize B SStar)) := by
      exact diagonal_weak_load_minus_le hFhat.1 hFhat.2
        (by
          simp only [Ehat, G0, g0, profileRecenteredMean,
            toFullBlockMat_blockMatMul,
            toFullBlockMat_blockMatTranspose_conj,
            toFullBlockMat_blockG, Matrix.mul_assoc])
        (pLoad e) (rMinus e) hload
    have hpair : vecDot (pLoad e) (rMinus e) = 1 := by
      simpa only [pLoad, rLoad, rMinus, rSym, B, centeredResponseLoadP,
        centeredResponseLoadQ, centeredResponseMetric,
        centeredResponseBlock, responseSymmetric] using
        dotProduct_signed_load (centeredResponseMetric_posDef hS hStar K)
          (skew_sub (by exact hg0) (is_skew_mat_response_skew K)) rfl rfl he
    have hLamRaw : LamM ≤
        Real.sqrt 5 * Real.sqrt (Real.sqrt (relSize B SStar)) :=
      profile_energy_load_le_sqrt_five htheta.1 hpair hLenSq
    have hcompare : blockImbalance (adaptedMean P q t) ≤
        (1 + deltaDet) ^ (d : ℝ) * blockImbalance (adaptedMean P q s) :=
      hcomp.1.trans (mul_le_mul_of_nonneg_right hrhoPow
        (canonImbalance_nonneg _))
    have hproducts := calibrated_load_products_of_raw
      (d := d) (R := 1 + deltaDet)
      (kappaT := blockImbalance (adaptedMean P q t))
      (kappaS := blockImbalance (adaptedMean P q s))
      (theta := relSize B SStar)
      (KStar := Real.sqrt
          (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
        (1 + deltaDet) ^ ((d : ℝ) / 4))
      (LenStar := 2 * Real.sqrt (Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2)))
      (LambdaStar := Real.sqrt 5 * Real.sqrt (Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2)))
      (by positivity) (canonImbalance_nonneg _) hkappa hR0 hbetaBound
      hcompare (hthetaRootAt e he) hKraw hLenRaw hLamRaw rfl rfl rfl
      hLen0 hLam0
    let Ft := adaptedMean P q t
    let Mtot := fun a : CoeffSpace d ↦ diagonalWeakMaximum ((1 + g) / 2) q t
      (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
    let Ucell := fun a : CoeffSpace d ↦ diagonalWeakCellSum q t H (1 / 2)
      (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
    let Uav := fun a : CoeffSpace d ↦ diagonalWeakAverageSum q t H (1 / 2)
      ((1 + g) / 2) (skewBlockCongr h0 Ft)
      (a.subSkew h0 h0.property)
    let Eminus := fun a : CoeffSpace d ↦ diagonalWeakEnergy hqpd' t
      (a.subSkew h0 h0.property) (pLoad e) (rMinus e)
    let N := eLpNorm (profilePrimalWeakRoot m0 hqpd' t
      (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rMinus e)
      (centerMinus e)) 2 P
    let cell := eLpNorm Ucell 2 P
    let average := eLpNorm Uav 2 P
    let bad := profileBadEnergy P Mtot Eminus
    let good := profileGoodEnergy P (initExpA g) H Mtot Eminus
    let center := profilePrimalCenterVariance P m0 hqpd' t
      (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rMinus e)
    let centeredRoot := centeredHistory P (initExpQ d g : ℝ)
      (initExpRhoMax d g) q jStar t ^ (initExpQ d g : ℝ)⁻¹
    let nonlinearRoot := nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ^ (initExpQ d g : ℝ)⁻¹
    let nonlinearHalf := nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ^ (2 * (initExpQ d g : ℝ))⁻¹
    let KStar := Real.sqrt
        (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
      (1 + deltaDet) ^ ((d : ℝ) / 4)
    let LenStar := 2 * Real.sqrt (Real.sqrt (3 / 2) *
      (1 + deltaDet) ^ ((d : ℝ) / 2))
    let LambdaStar := Real.sqrt 5 * Real.sqrt (Real.sqrt (3 / 2) *
      (1 + deltaDet) ^ ((d : ℝ) / 2))
    let Scen := centeredWindowCoefficient H (initExpRhoMax d g)
    let Scell := nonlinearCellWindowCoefficient H (initExpA g)
      (initExpQ d g : ℝ)
    let Sav := nonlinearAverageWindowCoefficient H (initExpA g)
      (initExpQ d g : ℝ)
    let etaRoot := eta ^ (initExpQ d g : ℝ)⁻¹
    let etaHalf := eta ^ (2 * (initExpQ d g : ℝ))⁻¹
    let BStar := (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) *
      eta ^ ((2 : ℝ)⁻¹)
    let expo := (3 : ℝ) ^ (-initExpA g * (H : ℝ))
    let UStar := (Scen + Scell) * etaRoot + Sav * etaHalf
    let cconst := (1 - (3 : ℝ) ^ (-(1 : ℝ) / 2))⁻¹
    have hsourceENN : profileSourceMoment P (initExpQ d g : ℝ)
        (initExpRhoMax d g) q jStar t Ft ≤
          ENNReal.ofReal (1 / 2 * etaRoot) := by
      apply hsource.trans
      exact ENNReal.ofReal_le_ofReal (by simpa only [Ft, etaRoot] using hsourceReal)
    have htotalRoot := total_root_le_of_cap
      (Nat.zero_lt_of_lt hQgt) hetaPos.le hcenteredCap hsourceENN
      hmaxGroup.2.2.1
    have htotal := total_le_of_root_le
      (Nat.zero_lt_of_lt hQgt) hetaPos.le htotalRoot
    have hbadMajorant : profileBadMajorant (initExpQ d g : ℝ)
        (profileTotalHistory P (initExpQ d g : ℝ)
          (initExpRhoMax d g) q jStar t Ft).toReal
        (linearDrift P (initExpRhoDr g) q jStar t) ≤ BStar := by
      dsimp only [Ft, BStar]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      exact bad_majorant_from_total_history
        (show (2 : ℝ) < (initExpQ d g : ℝ) by exact_mod_cast hQgt)
        hetaPos hetaHi htotal hdriftT
    have hbad : bad ≤ ENNReal.ofReal (Real.sqrt 2 * LamM * BStar) := by
      have hbadBase : bad ≤ ENNReal.ofReal
          (Real.sqrt 2 * LamM * profileBadMajorant (initExpQ d g : ℝ)
            (profileTotalHistory P (initExpQ d g : ℝ)
              (initExpRhoMax d g) q jStar t Ft).toReal
            (linearDrift P (initExpRhoDr g) q jStar t)) := by
        simpa only [bad, Mtot, Eminus, LamM, LenM, Fhat, Ft, h0,
          ← profileHattedBlock_adaptedMean, profileHattedBlock,
          initExpRhoDr, initExpA] using henergy.1
      apply hbadBase.trans
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hbadMajorant
          (mul_nonneg (Real.sqrt_nonneg 2) hLam0))
    have hgood : good ≤ ENNReal.ofReal (Real.sqrt 2 * expo * LamM) := by
      simpa only [good, expo, LamM, LenM, Eminus, Mtot, Fhat, Ft, h0,
        ← profileHattedBlock_adaptedMean, profileHattedBlock,
        initExpA] using henergy.2.2.1
    have hweakEq : weakMinus e = N ^ (2 : ℕ) := by
      simpa only [weakMinus, N, centerMinus] using
        (profilePrimalWeakQuantity_eq P m0 hqpd' t
          (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rMinus e))
    have hCresp0 : 0 ≤ Cresp := zero_le_one.trans hCresp
    have hKStar0 : 0 ≤ KStar := by
      dsimp only [KStar]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (Real.rpow_nonneg hR0 _)
    have hLenStar0 : 0 ≤ LenStar := by
      dsimp only [LenStar]
      exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hLambdaStar0 : 0 ≤ LambdaStar := by
      dsimp only [LambdaStar]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hScen0 : 0 ≤ Scen := by
      dsimp only [Scen, centeredWindowCoefficient]
      exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by norm_num) _)
    have hScell0 : 0 ≤ Scell := by
      dsimp only [Scell, nonlinearCellWindowCoefficient]
      exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by norm_num) _
    have hSav0 : 0 ≤ Sav := by
      dsimp only [Sav, nonlinearAverageWindowCoefficient]
      exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by norm_num) _
    have hetaRoot0 : 0 ≤ etaRoot := by
      dsimp only [etaRoot]
      exact Real.rpow_nonneg hetaPos.le _
    have hetaHalf0 : 0 ≤ etaHalf := by
      dsimp only [etaHalf]
      exact Real.rpow_nonneg hetaPos.le _
    have hBStar0 : 0 ≤ BStar := by
      dsimp only [BStar]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg hetaPos.le _)
    have hexpo0 : 0 ≤ expo := by
      dsimp only [expo]
      exact Real.rpow_nonneg (by norm_num) _
    have hcconstEq : cconst =
        (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
      dsimp only [cconst]
      norm_num
    have hcconst0 : 0 ≤ cconst :=
      zero_le_one.trans (cconst_bounds hcconstEq).1
    have hUStar0 : 0 ≤ UStar := by
      dsimp only [UStar]
      exact add_nonneg
        (mul_nonneg (add_nonneg hScen0 hScell0) hetaRoot0)
        (mul_nonneg hSav0 hetaHalf0)
    have hRStarEq : RStar = Cresp * KStar * LenStar * UStar +
        Cresp * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
          (BStar + expo) + cconst * KStar * LenStar * etaRoot := by
      rw [hcconstEq]
      rfl
    have hRStar0 : 0 ≤ RStar := by
      rw [hRStarEq]
      exact add_nonneg
        (add_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCresp0 hKStar0) hLenStar0) hUStar0)
          (mul_nonneg
            (div_nonneg
              (mul_nonneg
                (mul_nonneg (mul_nonneg hCresp0 hKStar0)
                  (Real.sqrt_nonneg 2)) hLambdaStar0)
              (mul_nonneg (by norm_num) (zero_lt_initExpA hg).le))
            (add_nonneg hBStar0 hexpo0)))
        (mul_nonneg
          (mul_nonneg (mul_nonneg hcconst0 hKStar0) hLenStar0) hetaRoot0)
    have hcell' : cell ≤ ENNReal.ofReal Scen * centeredRoot +
        ENNReal.ofReal Scell * nonlinearRoot := by
      simpa only [cell, Ucell, Scen, Scell, Ft] using hcell
    have hav' : average ≤ ENNReal.ofReal Sav * nonlinearHalf := by
      simpa only [average, Uav, Sav, Ft, one_div] using hav
    have hcenter' : center ≤ ENNReal.ofReal (Kfac * LenM) *
        centeredRoot := by
      simpa only [center, Kfac, LenM, centeredRoot, Fhat, Ft,
        ← profileHattedBlock_adaptedMean, profileHattedBlock] using hcenter.1
    have hN' : N ≤ ENNReal.ofReal (Cprof * Kfac * LenM) *
          (cell + average) +
        ENNReal.ofReal (Cprof * Kfac / (2 * initExpA g)) *
          (bad + good) + ENNReal.ofReal cconst * center := by
      simpa only [Cprof, N, cell, average, bad, good, center, Kfac, LenM,
        LamM, Fhat, Ft, Mtot, Ucell, Uav, Eminus, cconst, centerMinus,
        h0, initExpA,
        ← profileHattedBlock_adaptedMean, profileHattedBlock] using hN
    exact weak_quantity_le_rstar_sq_of_profile
      (W := weakMinus e) (N := N) (cell := cell) (average := average)
      (bad := bad) (good := good) (center := center)
      (centeredRoot := centeredRoot) (nonlinearRoot := nonlinearRoot)
      (nonlinearHalf := nonlinearHalf)
      (Cprof := Cprof) (Cresp := Cresp) (K := Kfac) (Len := LenM)
      (Lam := LamM) (KStar := KStar) (LenStar := LenStar)
      (LambdaStar := LambdaStar) (sqrtTwo := Real.sqrt 2)
      (alpha := initExpA g) (cconst := cconst) (Scen := Scen)
      (Scell := Scell) (Sav := Sav) (etaRoot := etaRoot)
      (etaHalf := etaHalf) (BStar := BStar) (expo := expo)
      (UStar := UStar) (RStar := RStar)
      (kappa := blockImbalance (adaptedMean P q s))
      hweakEq hRStar0
      (canonImbalance_nonneg _)
      (le_max_left _ _) hCresp0 hK0 hLen0 hLam0
      hKStar0 hLenStar0 hLambdaStar0
      (Real.sqrt_nonneg _) (zero_lt_initExpA hg)
      hcconst0 hScen0 hScell0 hSav0 hetaRoot0 hetaHalf0 hBStar0 hexpo0
      (by simpa only [KStar, LenStar, LambdaStar] using hproducts.1)
      (by simpa only [KStar, LenStar, LambdaStar] using hproducts.2)
      hcell' hav'
      (by simpa only [centeredRoot, etaRoot] using hcenteredRoot)
      (by simpa only [nonlinearRoot, etaRoot] using hnonlinearRoot)
      (by simpa only [nonlinearHalf, etaHalf] using hnonlinearHalf)
      hbad hgood hcenter' hN'
      rfl hRStarEq
  · intro e he
    rcases hprofileAt e with
      ⟨hsource, hmaxGroup, hcell, hav, henergy, _, hN, hcenter,
        _, _, _, _, _⟩
    obtain ⟨_, hcomp, htheta, _, hloadSq, hterminal, _, _⟩ :=
      hcalibrationAt e he
    let Fhat := profileRecenteredMean P q (canonicalShear E0) t
    let Kfac := diagonalWeakMetricFactor m0 Fhat
    let LenP := diagonalWeakLoadPlus Fhat (pLoad e) (rPlus e)
    let LamP := profileEnergyLoad LenP (pLoad e) (rPlus e)
    have hFhat := profileRecenteredMean_symm_posDef
      (g := canonicalShear E0) (hblocks t (by omega) le_rfl).2
    have hK0 : 0 ≤ Kfac := diagonalWeakMetricFactor_nonneg m0 Fhat
    have hLen0 : 0 ≤ LenP :=
      diagonalWeakLoadPlus_nonneg Fhat (pLoad e) (rPlus e)
    have hLam0 : 0 ≤ LamP :=
      profileEnergyLoad_nonneg LenP (pLoad e) (rPlus e)
    have hKsq : Kfac ^ 2 = relSize Ehat M0 := by
      rw [sq_diagonalWeakMetricFactor hm0pd' hFhat.1,
        blockSize_eq_relSize hFhat.1
          (isSymmetricBlockMat_diagonalMetric hm0pd')
          (blockPosDef_diagonalMetric hm0pd')
          (posDef_toFullBlockMat hFhat.1 hFhat.2).posSemidef]
      simp only [profileRecenteredMean, toFullBlockMat_blockMatMul,
        toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG,
        toFullBlockMat_blockDiag, Ehat, G0, g0, M0, hm0eq,
        canonicalMetric, Matrix.mul_assoc]
    have hKraw : Kfac ≤ Real.sqrt beta *
        Real.sqrt (Real.sqrt (blockImbalance (adaptedMean P q t))) :=
      profile_factor_le hm0pd' rfl hEhatPos.posSemidef hK0 hKsq hbeta0
        (by simpa only [beta, M0, Ehat, G0, g0, hm0eq,
          canonicalMetric, canonicalShear, blockImbalance] using hterminal.2)
    have hload : Sum.elim (pLoad e) (rPlus e) ⬝ᵥ Ehat *ᵥ
        Sum.elim (pLoad e) (rPlus e) ≤
          4 * Real.sqrt (relSize B SStar) := by
      simpa only [pLoad, rLoad, rPlus, Ehat, G0, B, rSym,
        hRsp, responseSkew] using hloadSq.2
    have hLenSq : LenP ^ 2 ≤ 4 * Real.sqrt (relSize B SStar) := by
      rw [sq_diagonalWeakLoadPlus hFhat.1 hFhat.2,
        blockVecDot_blockMatVecMul_eq_dotProduct]
      simpa only [LenP, Fhat, Ehat, G0, g0, profileRecenteredMean,
        toFullBlockMat_blockMatMul, toFullBlockMat_blockMatTranspose_conj,
        toFullBlockMat_blockG, Matrix.mul_assoc,
        to_full_block_vec_pair] using hload
    have hLenRaw : LenP ≤
        2 * Real.sqrt (Real.sqrt (relSize B SStar)) := by
      exact diagonal_weak_load_plus_le hFhat.1 hFhat.2
        (by
          simp only [Ehat, G0, g0, profileRecenteredMean,
            toFullBlockMat_blockMatMul,
            toFullBlockMat_blockMatTranspose_conj,
            toFullBlockMat_blockG, Matrix.mul_assoc])
        (pLoad e) (rPlus e) hload
    have hpair : vecDot (pLoad e) (rPlus e) = 1 := by
      simpa only [pLoad, rLoad, rPlus, rSym, B, centeredResponseLoadP,
        centeredResponseLoadQ, centeredResponseMetric,
        centeredResponseBlock, responseSymmetric] using
        dotProduct_signed_load (centeredResponseMetric_posDef hS hStar K)
          (skew_sub (is_skew_mat_response_skew K) (by exact hg0)) rfl rfl he
    have hLamRaw : LamP ≤
        Real.sqrt 5 * Real.sqrt (Real.sqrt (relSize B SStar)) :=
      profile_energy_load_le_sqrt_five htheta.1 hpair hLenSq
    have hcompare : blockImbalance (adaptedMean P q t) ≤
        (1 + deltaDet) ^ (d : ℝ) * blockImbalance (adaptedMean P q s) :=
      hcomp.1.trans (mul_le_mul_of_nonneg_right hrhoPow
        (canonImbalance_nonneg _))
    have hproducts := calibrated_load_products_of_raw
      (d := d) (R := 1 + deltaDet)
      (kappaT := blockImbalance (adaptedMean P q t))
      (kappaS := blockImbalance (adaptedMean P q s))
      (theta := relSize B SStar)
      (KStar := Real.sqrt
          (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
        (1 + deltaDet) ^ ((d : ℝ) / 4))
      (LenStar := 2 * Real.sqrt (Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2)))
      (LambdaStar := Real.sqrt 5 * Real.sqrt (Real.sqrt (3 / 2) *
        (1 + deltaDet) ^ ((d : ℝ) / 2)))
      (by positivity) (canonImbalance_nonneg _) hkappa hR0 hbetaBound
      hcompare (hthetaRootAt e he) hKraw hLenRaw hLamRaw rfl rfl rfl
      hLen0 hLam0
    let Ft := adaptedMean P q t
    let Mtot := fun a : CoeffSpace d ↦ diagonalWeakMaximum ((1 + g) / 2) q t
      (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
    let Ucell := fun a : CoeffSpace d ↦ diagonalWeakCellSum q t H (1 / 2)
      (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
    let Uav := fun a : CoeffSpace d ↦ diagonalWeakAverageSum q t H (1 / 2)
      ((1 + g) / 2) (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
    let Eplus := fun a : CoeffSpace d ↦ diagonalWeakAdjointEnergy hqpd' t
      (a.subSkew h0 h0.property) (pLoad e) (rPlus e)
    let N := eLpNorm (profileAdjointWeakRoot m0 hqpd' t
      (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rPlus e)
      (centerPlus e)) 2 P
    let cell := eLpNorm Ucell 2 P
    let average := eLpNorm Uav 2 P
    let bad := profileBadEnergy P Mtot Eplus
    let good := profileGoodEnergy P (initExpA g) H Mtot Eplus
    let center := profileAdjointCenterVariance P m0 hqpd' t
      (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rPlus e)
    let centeredRoot := centeredHistory P (initExpQ d g : ℝ)
      (initExpRhoMax d g) q jStar t ^ (initExpQ d g : ℝ)⁻¹
    let nonlinearRoot := nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ^ (initExpQ d g : ℝ)⁻¹
    let nonlinearHalf := nonlinearHistory P (initExpQ d g : ℝ)
      (initExpA g) q jStar t ^ (2 * (initExpQ d g : ℝ))⁻¹
    let KStar := Real.sqrt
        (Real.sqrt 2 * (1 + deltaDet) ^ ((d : ℝ) / 2)) *
      (1 + deltaDet) ^ ((d : ℝ) / 4)
    let LenStar := 2 * Real.sqrt (Real.sqrt (3 / 2) *
      (1 + deltaDet) ^ ((d : ℝ) / 2))
    let LambdaStar := Real.sqrt 5 * Real.sqrt (Real.sqrt (3 / 2) *
      (1 + deltaDet) ^ ((d : ℝ) / 2))
    let Scen := centeredWindowCoefficient H (initExpRhoMax d g)
    let Scell := nonlinearCellWindowCoefficient H (initExpA g)
      (initExpQ d g : ℝ)
    let Sav := nonlinearAverageWindowCoefficient H (initExpA g)
      (initExpQ d g : ℝ)
    let etaRoot := eta ^ (initExpQ d g : ℝ)⁻¹
    let etaHalf := eta ^ (2 * (initExpQ d g : ℝ))⁻¹
    let BStar := (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) * eta ^ ((2 : ℝ)⁻¹)
    let expo := (3 : ℝ) ^ (-initExpA g * (H : ℝ))
    let UStar := (Scen + Scell) * etaRoot + Sav * etaHalf
    let cconst := (1 - (3 : ℝ) ^ (-(1 : ℝ) / 2))⁻¹
    have hsourceENN : profileSourceMoment P (initExpQ d g : ℝ)
        (initExpRhoMax d g) q jStar t Ft ≤ ENNReal.ofReal (1 / 2 * etaRoot) := by
      exact hsource.trans (ENNReal.ofReal_le_ofReal
        (by simpa only [Ft, etaRoot] using hsourceReal))
    have htotalRoot := total_root_le_of_cap
      (Nat.zero_lt_of_lt hQgt) hetaPos.le hcenteredCap hsourceENN
      hmaxGroup.2.2.1
    have htotal := total_le_of_root_le
      (Nat.zero_lt_of_lt hQgt) hetaPos.le htotalRoot
    have hbadMajorant : profileBadMajorant (initExpQ d g : ℝ)
        (profileTotalHistory P (initExpQ d g : ℝ)
          (initExpRhoMax d g) q jStar t Ft).toReal
        (linearDrift P (initExpRhoDr g) q jStar t) ≤ BStar := by
      dsimp only [Ft, BStar]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      exact bad_majorant_from_total_history
        (show (2 : ℝ) < (initExpQ d g : ℝ) by exact_mod_cast hQgt)
        hetaPos hetaHi htotal hdriftT
    have hbad : bad ≤ ENNReal.ofReal (Real.sqrt 2 * LamP * BStar) := by
      have hbadBase : bad ≤ ENNReal.ofReal
          (Real.sqrt 2 * LamP * profileBadMajorant (initExpQ d g : ℝ)
            (profileTotalHistory P (initExpQ d g : ℝ)
              (initExpRhoMax d g) q jStar t Ft).toReal
            (linearDrift P (initExpRhoDr g) q jStar t)) := by
        simpa only [bad, Mtot, Eplus, LamP, LenP, Fhat, Ft, h0,
          ← profileHattedBlock_adaptedMean, profileHattedBlock,
          initExpRhoDr, initExpA] using henergy.2.1
      exact hbadBase.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hbadMajorant
          (mul_nonneg (Real.sqrt_nonneg 2) hLam0)))
    have hgood : good ≤ ENNReal.ofReal (Real.sqrt 2 * expo * LamP) := by
      simpa only [good, expo, LamP, LenP, Eplus, Mtot, Fhat, Ft, h0,
        ← profileHattedBlock_adaptedMean, profileHattedBlock,
        initExpA] using henergy.2.2.2
    have hweakEq : weakPlus e = N ^ (2 : ℕ) := by
      simpa only [weakPlus, N, centerPlus] using
        (profileAdjointWeakQuantity_eq P m0 hqpd' t
          (fun a ↦ a.subSkew h0 h0.property) (pLoad e) (rPlus e))
    have hCresp0 : 0 ≤ Cresp := zero_le_one.trans hCresp
    have hKStar0 : 0 ≤ KStar := by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hR0 _)
    have hLenStar0 : 0 ≤ LenStar := by
      exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hLambdaStar0 : 0 ≤ LambdaStar := by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hScen0 : 0 ≤ Scen := by
      exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by norm_num) _)
    have hScell0 : 0 ≤ Scell := by
      exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by norm_num) _
    have hSav0 : 0 ≤ Sav := by
      exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by norm_num) _
    have hetaRoot0 : 0 ≤ etaRoot := Real.rpow_nonneg hetaPos.le _
    have hetaHalf0 : 0 ≤ etaHalf := Real.rpow_nonneg hetaPos.le _
    have hBStar0 : 0 ≤ BStar := mul_nonneg
      (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hetaPos.le _)
    have hexpo0 : 0 ≤ expo := Real.rpow_nonneg (by norm_num) _
    have hcconstEq : cconst =
        (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
      dsimp only [cconst]
      norm_num
    have hcconst0 : 0 ≤ cconst :=
      zero_le_one.trans (cconst_bounds hcconstEq).1
    have hUStar0 : 0 ≤ UStar := add_nonneg
      (mul_nonneg (add_nonneg hScen0 hScell0) hetaRoot0)
      (mul_nonneg hSav0 hetaHalf0)
    have hRStarEq : RStar = Cresp * KStar * LenStar * UStar +
        Cresp * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
          (BStar + expo) + cconst * KStar * LenStar * etaRoot := by
      rw [hcconstEq]
      rfl
    have hRStar0 : 0 ≤ RStar := by
      rw [hRStarEq]
      exact add_nonneg
        (add_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg hCresp0 hKStar0) hLenStar0) hUStar0)
          (mul_nonneg
            (div_nonneg
              (mul_nonneg (mul_nonneg (mul_nonneg hCresp0 hKStar0)
                (Real.sqrt_nonneg 2)) hLambdaStar0)
              (mul_nonneg (by norm_num) (zero_lt_initExpA hg).le))
            (add_nonneg hBStar0 hexpo0)))
        (mul_nonneg (mul_nonneg (mul_nonneg hcconst0 hKStar0) hLenStar0)
          hetaRoot0)
    have hcell' : cell ≤ ENNReal.ofReal Scen * centeredRoot +
        ENNReal.ofReal Scell * nonlinearRoot := by
      simpa only [cell, Ucell, Scen, Scell, Ft] using hcell
    have hav' : average ≤ ENNReal.ofReal Sav * nonlinearHalf := by
      simpa only [average, Uav, Sav, Ft, one_div] using hav
    have hcenter' : center ≤ ENNReal.ofReal (Kfac * LenP) * centeredRoot := by
      simpa only [center, Kfac, LenP, centeredRoot, Fhat, Ft,
        ← profileHattedBlock_adaptedMean, profileHattedBlock] using hcenter.2
    have hN' : N ≤ ENNReal.ofReal (Cprof * Kfac * LenP) *
          (cell + average) +
        ENNReal.ofReal (Cprof * Kfac / (2 * initExpA g)) *
          (bad + good) + ENNReal.ofReal cconst * center := by
      simpa only [Cprof, N, cell, average, bad, good, center, Kfac, LenP,
        LamP, Fhat, Ft, Mtot, Ucell, Uav, Eplus, cconst, centerPlus,
        h0, initExpA, ← profileHattedBlock_adaptedMean,
        profileHattedBlock] using hN
    exact weak_quantity_le_rstar_sq_of_profile
      (W := weakPlus e) (N := N) (cell := cell) (average := average)
      (bad := bad) (good := good) (center := center)
      (centeredRoot := centeredRoot) (nonlinearRoot := nonlinearRoot)
      (nonlinearHalf := nonlinearHalf) (Cprof := Cprof) (Cresp := Cresp)
      (K := Kfac) (Len := LenP) (Lam := LamP) (KStar := KStar)
      (LenStar := LenStar) (LambdaStar := LambdaStar)
      (sqrtTwo := Real.sqrt 2) (alpha := initExpA g) (cconst := cconst)
      (Scen := Scen) (Scell := Scell) (Sav := Sav) (etaRoot := etaRoot)
      (etaHalf := etaHalf) (BStar := BStar) (expo := expo)
      (UStar := UStar) (RStar := RStar)
      (kappa := blockImbalance (adaptedMean P q s))
      hweakEq hRStar0 (canonImbalance_nonneg _) (le_max_left _ _) hCresp0
      hK0 hLen0 hLam0 hKStar0 hLenStar0 hLambdaStar0
      (Real.sqrt_nonneg _) (zero_lt_initExpA hg) hcconst0 hScen0 hScell0
      hSav0 hetaRoot0 hetaHalf0 hBStar0 hexpo0
      (by simpa only [KStar, LenStar, LambdaStar] using hproducts.1)
      (by simpa only [KStar, LenStar, LambdaStar] using hproducts.2)
      hcell' hav'
      (by simpa only [centeredRoot, etaRoot] using hcenteredRoot)
      (by simpa only [nonlinearRoot, etaRoot] using hnonlinearRoot)
      (by simpa only [nonlinearHalf, etaHalf] using hnonlinearHalf)
      hbad hgood hcenter' hN' rfl hRStarEq

end

end Homogenization.HighContrast.Response
