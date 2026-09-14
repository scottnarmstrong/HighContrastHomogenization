/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseCompactInsertion
import HCPoly.Provider.Response.RandomAdaptedResponseProfileScalar
import HCPoly.Provider.Response.EndgameGlue
import HCPoly.Provider.Response.LoadCalibration
import HCPoly.Provider.Response.WindowAbsorption
import HCPoly.Provider.ShortHop.Normalization
import HCPoly.Provider.ShortHop.PathStep

/-!
# Fixed-window response endgame

This module isolates the deterministic terminal part of the adapted-response
argument.  Its response input is the literal supremum of the independently
centered primal and adjoint calls at the Schur loads of the terminal block.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory Set

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- The profile and pre-Young constants are merged before any source constant
is introduced, and the response window is chosen at that merged constant. -/
theorem exists_merged_response_window {d : ℕ} (hd : 2 ≤ d)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {deltaAd Cprof Cpre : ℝ} (hdeltaAd : 0 < deltaAd)
    (hCprof : 1 ≤ Cprof) :
    ∃ (Cresp epsCal deltaDet : ℝ) (H : ℕ) (eta etaDr : ℝ),
      Cresp = max Cprof Cpre ∧ 1 ≤ Cresp ∧ Cprof ≤ Cresp ∧ Cpre ≤ Cresp ∧
      0 < epsCal ∧ epsCal ≤ 1 / 3 ∧ 0 < deltaDet ∧ deltaDet ≤ 1 ∧
      4 ≤ H ∧ 0 < eta ∧ eta ≤ 1 / 2 ∧
      0 < etaDr ∧ etaDr ≤ min 1 (eta / 2) ∧
      ∀ cconst GammaStar cepsStar betaStar chiTheta AStar TStar LStar KStar
        LenStar LambdaStar Scen Scell Sav UStar BStar RStar omegaRsp : ℝ,
        cconst = (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ →
        GammaStar = 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1 →
        cepsStar = Real.sqrt 2 →
        betaStar = cepsStar * (1 + deltaDet) ^ ((d : ℝ) / 2) →
        chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2) →
        AStar = 2 * chiTheta →
        TStar = 2 * ((1 + deltaDet) ^ (d : ℝ) - 1) * chiTheta →
        LStar = 32 * GammaStar * cepsStar * betaStar *
          (1 + deltaDet) ^ ((d : ℝ) / 2) * chiTheta →
        KStar = Real.sqrt betaStar * (1 + deltaDet) ^ ((d : ℝ) / 4) →
        LenStar = 2 * Real.sqrt chiTheta →
        LambdaStar = Real.sqrt 5 * Real.sqrt chiTheta →
        Scen = 2 * ∑ r ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-(1 / 2 - initExpRhoMax d g) * (r : ℝ)) →
        Scell = ∑ r ∈ Finset.Icc 1 H,
          (3 : ℝ) ^ (-(r : ℝ) / 2 +
            initExpA g * ((r : ℝ) - 1) / (initExpQ d g : ℝ)) →
        Sav = ∑ r ∈ Finset.Icc 1 H,
          (3 : ℝ) ^ (-initExpA g * (r : ℝ) +
            initExpA g * ((r : ℝ) - 1) / (2 * (initExpQ d g : ℝ))) →
        UStar = (Scen + Scell) * eta ^ ((initExpQ d g : ℝ)⁻¹) +
          Sav * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) →
        BStar = (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) * eta ^ ((2 : ℝ)⁻¹) →
        RStar = Cresp * KStar * LenStar * UStar +
          Cresp * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
            (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) +
          cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹) →
        omegaRsp = 2 * Cresp * (TStar + Real.sqrt (TStar * AStar) +
          Real.sqrt (TStar * LStar) +
          (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar)) +
          RStar ^ 2) →
        12 * (d : ℝ) * omegaRsp * (1 + deltaDet) ^ (2 * (d : ℝ)) *
          (1 + deltaAd⁻¹) < 1 := by
  let Cresp : ℝ := max Cprof Cpre
  obtain ⟨hCresp, hprof, hpre⟩ :=
    one_le_response_constant hCprof (show Cresp = max Cprof Cpre from rfl)
  obtain ⟨epsCal, deltaDet, H, eta, etaDr, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, habs⟩ := exists_response_window hd hg hdeltaAd hCresp
  exact ⟨Cresp, epsCal, deltaDet, H, eta, etaDr, rfl, hCresp, hprof, hpre,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, habs⟩

/-- Once the two centered responses obey the numerical response bound, the
terminal determinant comparison and calibration close the imbalance. -/
theorem random_adapted_response_endgame {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {s t : ℤ}
    {E0 : BlockMat d} (hE0symm : IsSymmetricBlockMat E0)
    (hE0pd : BlockPosDef E0)
    (hfinT : HasFiniteAdaptedMean P q t)
    (hEspd : BlockPosDef (adaptedMean P q s))
    (hEtpd : BlockPosDef (adaptedMean P q t))
    (hts : BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q s))
    (hsSharp : BlockMatLoewnerLE (blockSharp (adaptedMean P q s))
      (adaptedMean P q s))
    (htSharp : BlockMatLoewnerLE (blockSharp (adaptedMean P q t))
      (adaptedMean P q t))
    {epsCal deltaDet deltaAd omegaRsp : ℝ}
    (hepsPos : 0 < epsCal) (hepsHi : epsCal ≤ 1 / 3)
    (hcalLo : BlockMatLoewnerLE (blockScale (1 - epsCal) E0)
      (adaptedMean P q s))
    (hcalHi : BlockMatLoewnerLE (adaptedMean P q s)
      (blockScale (1 + epsCal) E0))
    (hdet : adaptedDetRoot P q s <
      (1 + deltaDet) * adaptedDetRoot P q t)
    (hdeltaDet : 0 ≤ deltaDet) (hdeltaAd : 0 < deltaAd)
    (homega : 0 ≤ omegaRsp)
    (habsorb : 12 * (d : ℝ) * omegaRsp *
      (1 + deltaDet) ^ (2 * (d : ℝ)) * (1 + deltaAd⁻¹) < 1)
    (hresponse : ∀ (S SStar K : Mat d), S.PosDef → SStar.PosDef →
      toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K →
      sSup
          ((fun e : Vec d ↦
              |centeredResponse P (adaptedDomain hq t)
                  (centeredResponseLoadP S SStar K e)
                  (centeredResponseLoadQ S SStar K e -
                    responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| +
              |centeredAdjointResponse P (adaptedDomain hq t)
                  (centeredResponseLoadP S SStar K e)
                  (centeredResponseLoadQ S SStar K e +
                    responseSkew K *ᵥ centeredResponseLoadP S SStar K e)|) ''
            {e : Vec d | e ⬝ᵥ e = 1}) ≤
        omegaRsp * blockImbalance (adaptedMean P q s)) :
    blockImbalance (adaptedMean P q t) ≤ 1 + deltaAd := by
  have hE0full : (toFullBlockMat E0).PosDef :=
    posDef_toFullBlockMat hE0symm hE0pd
  have hEsPos : (toFullBlockMat (adaptedMean P q s)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hEspd
  have hEtPos : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEtpd
  obtain ⟨S, SStar, K, hS, hStar, hEtform⟩ := exists_schurBlock hEtPos
  let r : Mat d := (2 : ℝ)⁻¹ • (K + Kᴴ)
  let h : Mat d := (2 : ℝ)⁻¹ • (K - Kᴴ)
  let B : Mat d := S + rᴴ * SStar⁻¹ * r
  let m : Mat d := matGeomMean B SStar
  let g0 : Mat d := canonicalShear E0
  let m0 : Mat d := canonicalMetric E0
  let G0 : FullBlockMat d := fullBlockShear g0
  let M0 : FullBlockMat d := Matrix.fromBlocks m0 0 0 m0⁻¹
  let Ehat : FullBlockMat d := G0ᴴ * toFullBlockMat (adaptedMean P q t) * G0
  let Eshat : FullBlockMat d := G0ᴴ * toFullBlockMat (adaptedMean P q s) * G0
  let ceps : ℝ := Real.sqrt ((1 + epsCal) / (1 - epsCal))
  let rho : ℝ := canonDetRatio (toFullBlockMat (adaptedMean P q s))
    (toFullBlockMat (adaptedMean P q t))
  let beta : ℝ := ceps * Real.sqrt (rho ^ d)
  let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  let e0 : Vec d := Pi.single i0 1
  have he0 : e0 ⬝ᵥ e0 = 1 := by
    simp [e0, dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  let p0 : Vec d := matSqrt m⁻¹ *ᵥ e0
  let q0 : Vec d := matSqrt m *ᵥ e0
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
  have hratio : rho < 1 + deltaDet := by
    have hrootT : 0 < adaptedDetRoot P q t := ShortHop.detRoot_pos hEtPos
    rw [show rho = adaptedDetRoot P q s / adaptedDetRoot P q t by
      exact canonDetRatio_eq_adaptedDetRoot_div rfl rfl hEsPos hEtPos]
    exact (div_lt_iff₀ hrootT).2 hdet
  have hsSharpFull : fullBlockSharp (toFullBlockMat (adaptedMean P q s)) ≤
      toFullBlockMat (adaptedMean P q s) := by
    simpa only [toFullBlockMat_blockSharp] using
      (le_of_blockMatLoewnerLE
        (isSymmetricBlockMat_blockSharp
          (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hEspd)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hsSharp)
  have htSharpFull : fullBlockSharp (toFullBlockMat (adaptedMean P q t)) ≤
      toFullBlockMat (adaptedMean P q t) := by
    simpa only [toFullBlockMat_blockSharp] using
      (le_of_blockMatLoewnerLE
        (isSymmetricBlockMat_blockSharp
          (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEtpd)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t) htSharp)
  obtain ⟨_, hcomp, htheta, _, _, _, _, _⟩ :=
    response_load_calibration hd hE0full hEsPos hEtPos
      (le_of_blockMatLoewnerLE (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hts)
      hsSharpFull htSharpFull
      hepsPos.le (by linarith only [hepsHi]) hlow hhigh rfl rfl rfl hS hStar
      hEtform rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl he0 rfl rfl
  have hcanon : blockImbalance (adaptedMean P q s) ≤
      (1 + deltaDet) ^ (2 * (d : ℝ)) *
        blockImbalance (adaptedMean P q t) := by
    rw [blockImbalance, blockImbalance]
    have hrho0 : 0 ≤ rho := by
      change 0 ≤ canonDetRatio (toFullBlockMat (adaptedMean P q s))
        (toFullBlockMat (adaptedMean P q t))
      rw [canonDetRatio]
      exact Real.rpow_nonneg (div_nonneg hEsPos.det_pos.le hEtPos.det_pos.le) _
    have hpow : rho ^ (2 * d) ≤ (1 + deltaDet) ^ (2 * d) :=
      pow_le_pow_left₀ hrho0 (le_of_lt hratio) _
    have hnat : ((1 + deltaDet) ^ (2 * d) : ℝ) =
        (1 + deltaDet) ^ (2 * (d : ℝ)) := by
      rw [← Real.rpow_natCast]
      norm_num
    have hkappaT0 : 0 ≤ canonImbalance
        (toFullBlockMat (adaptedMean P q t)) :=
      canonImbalance_nonneg _
    calc
      canonImbalance (toFullBlockMat (adaptedMean P q s)) ≤
          rho ^ (2 * d) * canonImbalance
            (toFullBlockMat (adaptedMean P q t)) := hcomp.2
      _ ≤ (1 + deltaDet) ^ (2 * d) *
          canonImbalance (toFullBlockMat (adaptedMean P q t)) :=
        mul_le_mul_of_nonneg_right hpow hkappaT0
      _ = (1 + deltaDet) ^ (2 * (d : ℝ)) *
          canonImbalance (toFullBlockMat (adaptedMean P q t)) := by rw [hnat]
  let Ssup : ℝ := sSup
    ((fun e : Vec d ↦
        |centeredResponse P (adaptedDomain hq t)
            (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e -
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| +
        |centeredAdjointResponse P (adaptedDomain hq t)
            (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e +
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)|) ''
      {e : Vec d | e ⬝ᵥ e = 1})
  have hnorm := centeredResponse_absolute_bound hd (adaptedDomain hq t) hfinT
    hS hStar (by simpa [adaptedDomain] using! hEtform)
  have hnormEq := norm_normalized_sub_one hS hStar (K := K) (r := r)
    (B := B) rfl (by simpa only [← hEtform] using htSharpFull)
  have habs : relSize B SStar - 1 ≤ 2 * (d : ℝ) * Ssup := by
    rw [← hnormEq]
    exact hnorm
  have hkappaTheta : blockImbalance (adaptedMean P q t) ≤
      1 + 6 * (relSize B SStar - 1) := by
    rw [blockImbalance]
    dsimp only [B, r]
    linarith only [htheta.2.2]
  have hfactor : blockImbalance (adaptedMean P q t) - 1 ≤
      12 * (d : ℝ) * Ssup := twelve_d_chain hkappaTheta habs
  exact imbalance_le_of_absorption_rpow hdeltaAd hdeltaDet habsorb homega
    hfactor (hresponse S SStar K hS hStar hEtform) hcanon

end

end Homogenization.HighContrast.Response
