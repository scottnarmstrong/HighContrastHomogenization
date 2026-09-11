/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileEnergyWindow
import HCPoly.Provider.Response.ProfileWeakSkewLp
import HCPoly.Provider.Response.ProfileRecentSkewLp
import HCPoly.Provider.Response.ProfileCenterSkewLp
import HCPoly.Provider.Response.ProfileDefectHistory
import HCPoly.Provider.Response.ProfileRowSkewConclusion
import HCPoly.Provider.Response.ProfileMismatch
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger

/-!
# Terminal profile response assembly

This module assembles the complete fixed-window profile estimates.  Its
dimensional weak-profile coefficient is chosen before the probability law,
source data, terminal geometry, skew, and four independent load vectors.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

/-- Enlarging the dimensional coefficient enlarges either full weak-profile
right-hand side. -/
theorem profile_weak_rhs_mono
    {C0 C K L alpha : ℝ} (hC : C0 ≤ C) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (halpha : 0 < alpha) (U R V : ℝ≥0∞) :
    ENNReal.ofReal (C0 * K * L) * U +
          ENNReal.ofReal (C0 * K / (2 * alpha)) * R + V ≤
      ENNReal.ofReal (C * K * L) * U +
          ENNReal.ofReal (C * K / (2 * alpha)) * R + V := by
  have hcoef1 : C0 * K * L ≤ C * K * L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC hK) hL
  have hden : 0 ≤ 2 * alpha := by positivity
  have hcoef2 : C0 * K / (2 * alpha) ≤ C * K / (2 * alpha) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC hK) hden
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoef1) (zero_le U))
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoef2) (zero_le R)))
    le_rfl

/-- Complete terminal profiles give the source, maximum, recent, energy,
weak, centering, defect, row, and same-cell estimates with one dimensional
coefficient. -/
theorem exists_profile_response_constant {d : ℕ} (hd : 2 ≤ d) :
    ∃ Cprof : ℝ, 1 ≤ Cprof ∧
      ∀ (Q : ℕ), Even Q → 2 < Q →
      ∀ (P : Measure (CoeffSpace d)), IsProbabilityMeasure P →
      ∀ (g : ℝ), g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ (E : BlockMat d) (Psi : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ) (Csrc : ℝ),
      HCPoly.Frozen.IsStationaryLaw P →
      HCPoly.Frozen.IsUnitRangeLaw P →
      HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S →
      1 ≤ Csrc →
      ∀ (jStar M : ℤ), IsCoupledWindow d (Q : ℝ) K jStar M →
      ∀ (Y : CoeffSpace d → ℝ),
      IsWindowMultiplier P g E Psi K Csrc jStar M Y →
      1 ≤ ∫ a, Y a ∂P →
      ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P (Q : ℝ) Y →
      lqNorm P (Q : ℝ) Y ≤ 2 →
      ∀ (rhoMax : ℝ), g < rhoMax → rhoMax < (1 + g) / 2 →
      (1 - g) / 4 ≤ (Q : ℝ) * rhoMax - d →
      ∀ (E0 : BlockMat d) (m0 q : Mat d),
      IsSymmetricBlockMat E0 → BlockPosDef E0 →
      m0 = canonicalMetric E0 → q = roundedGrid jStar m0 →
      (hgrid : IsRoundedGrid jStar q) →
      ∀ (s t : ℤ) (H : ℕ), jStar ≤ s → t = s + (H : ℤ) →
      4 ≤ H → (H : ℤ) < t →
      (∀ k : ℤ, jStar ≤ k → k ≤ t →
        adaptedCell q k ⊆ centeredCube d M) →
      (∀ k : ℤ, k < jStar → ∀ v : ℤ, v = s ∨ v = t →
        ∀ z ∈ containedCenters q k v,
          adaptedCellTranslate q k z ⊆ centeredCube d M) →
      (∀ k : ℤ, jStar ≤ k → k ≤ t →
        HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k)) →
      (∀ k : ℤ, jStar ≤ k → k ≤ t →
        BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k)) →
      IsWindowedSourceFields P g Csrc E jStar m0 s t Y →
      ∀ (Cport : ℝ), 1 ≤ Cport →
      portableHistory P (Q : ℝ) ((1 - g) / 4) rhoMax q jStar t ≤
        ENNReal.ofReal Cport *
          portableProfile P (Q : ℝ) ((1 - g) / 4) rhoMax q jStar s t →
      ∀ (h0 : {h : Mat d // IsSkewMat h})
        (pMinus qMinus pPlus qPlus : Vec d),
      let Qr : ℝ := Q
      let alpha := (1 - g) / 4
      let rhoWn := (1 + g) / 2
      let rhoDr := alpha / 2
      let hq := Recurrence.posDef_of_isRoundedGrid hgrid
      let Ft := adaptedMean P q t
      let Mtot := fun a ↦ diagonalWeakMaximum rhoWn q t
        (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
      let Ucell := fun a ↦ diagonalWeakCellSum q t H (1 / 2)
        (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
      let Uav := fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rhoWn
        (skewBlockCongr h0 Ft) (a.subSkew h0 h0.property)
      let Eminus := fun a ↦ diagonalWeakEnergy hq t
        (a.subSkew h0 h0.property) pMinus qMinus
      let Eplus := fun a ↦ diagonalWeakAdjointEnergy hq t
        (a.subSkew h0 h0.property) pPlus qPlus
      let Xminus := profilePrimalCenter P hq t
        (fun a ↦ a.subSkew h0 h0.property) pMinus qMinus
      let Xplus := profileAdjointCenter P hq t
        (fun a ↦ a.subSkew h0 h0.property) pPlus qPlus
      profileSourceMoment P Qr rhoMax q jStar t Ft ≤
          ENNReal.ofReal (4 * kappaRef E * boundaryConst Csrc g m0 ^ 2 *
            (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ)))) ∧
      ((∀ a, Mtot a ≤ profileTotalMaximum P rhoMax q jStar t Ft a +
          ENNReal.ofReal (linearDrift P rhoDr q jStar t)) ∧
        eLpNorm Mtot (ENNReal.ofReal Qr) P ≤
          profileTotalHistory P Qr rhoMax q jStar t Ft ^ Qr⁻¹ +
            ENNReal.ofReal (linearDrift P rhoDr q jStar t) ∧
        profileTotalHistory P Qr rhoMax q jStar t Ft ^ Qr⁻¹ ≤
          centeredHistory P Qr rhoMax q jStar t ^ Qr⁻¹ +
            profileSourceMoment P Qr rhoMax q jStar t Ft ∧
        eLpNorm Mtot (ENNReal.ofReal Qr) P ≤
          centeredHistory P Qr rhoMax q jStar t ^ Qr⁻¹ +
            profileSourceMoment P Qr rhoMax q jStar t Ft +
            ENNReal.ofReal (linearDrift P rhoDr q jStar t)) ∧
      eLpNorm Ucell 2 P ≤
        ENNReal.ofReal (centeredWindowCoefficient H rhoMax) *
            centeredHistory P Qr rhoMax q jStar t ^ Qr⁻¹ +
          ENNReal.ofReal (nonlinearCellWindowCoefficient H alpha Qr) *
            nonlinearHistory P Qr alpha q jStar t ^ Qr⁻¹ ∧
      eLpNorm Uav 2 P ≤
        ENNReal.ofReal (nonlinearAverageWindowCoefficient H alpha Qr) *
          nonlinearHistory P Qr alpha q jStar t ^ (1 / (2 * Qr)) ∧
      (let hTot := (profileTotalHistory P Qr rhoMax q jStar t Ft).toReal
       let beta := linearDrift P rhoDr q jStar t
       profileBadEnergy P Mtot Eminus ≤ ENNReal.ofReal (Real.sqrt 2 *
            profileEnergyLoad
              (diagonalWeakLoadMinus (skewBlockCongr h0 Ft) pMinus qMinus)
              pMinus qMinus * profileBadMajorant Qr hTot beta) ∧
       profileBadEnergy P Mtot Eplus ≤ ENNReal.ofReal (Real.sqrt 2 *
            profileEnergyLoad
              (diagonalWeakLoadPlus (skewBlockCongr h0 Ft) pPlus qPlus)
              pPlus qPlus * profileBadMajorant Qr hTot beta) ∧
       profileGoodEnergy P alpha H Mtot Eminus ≤ ENNReal.ofReal
          (Real.sqrt 2 * (3 : ℝ) ^ (-alpha * (H : ℝ)) *
            profileEnergyLoad
              (diagonalWeakLoadMinus (skewBlockCongr h0 Ft) pMinus qMinus)
              pMinus qMinus) ∧
       profileGoodEnergy P alpha H Mtot Eplus ≤ ENNReal.ofReal
          (Real.sqrt 2 * (3 : ℝ) ^ (-alpha * (H : ℝ)) *
            profileEnergyLoad
              (diagonalWeakLoadPlus (skewBlockCongr h0 Ft) pPlus qPlus)
              pPlus qPlus)) ∧
      eLpNorm (profilePrimalWeakRoot m0 hq t
          (fun a ↦ a.subSkew h0 h0.property) pMinus qMinus
          (profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 h0.property)
            pMinus qMinus)) 2 P ≤
        ENNReal.ofReal (Cprof * diagonalWeakMetricFactor m0
            (skewBlockCongr h0 Ft) *
          diagonalWeakLoadMinus (skewBlockCongr h0 Ft) pMinus qMinus) *
            (eLpNorm Ucell 2 P + eLpNorm Uav 2 P) +
          ENNReal.ofReal (Cprof * diagonalWeakMetricFactor m0
            (skewBlockCongr h0 Ft) / (2 * alpha)) *
            (profileBadEnergy P Mtot Eminus +
              profileGoodEnergy P alpha H Mtot Eminus) +
          ENNReal.ofReal constantSeminormCoefficient *
            profilePrimalCenterVariance P m0 hq t
              (fun a ↦ a.subSkew h0 h0.property) pMinus qMinus ∧
      eLpNorm (profileAdjointWeakRoot m0 hq t
          (fun a ↦ a.subSkew h0 h0.property) pPlus qPlus
          (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 h0.property)
            pPlus qPlus)) 2 P ≤
        ENNReal.ofReal (Cprof * diagonalWeakMetricFactor m0
            (skewBlockCongr h0 Ft) *
          diagonalWeakLoadPlus (skewBlockCongr h0 Ft) pPlus qPlus) *
            (eLpNorm Ucell 2 P + eLpNorm Uav 2 P) +
          ENNReal.ofReal (Cprof * diagonalWeakMetricFactor m0
            (skewBlockCongr h0 Ft) / (2 * alpha)) *
            (profileBadEnergy P Mtot Eplus +
              profileGoodEnergy P alpha H Mtot Eplus) +
          ENNReal.ofReal constantSeminormCoefficient *
            profileAdjointCenterVariance P m0 hq t
              (fun a ↦ a.subSkew h0 h0.property) pPlus qPlus ∧
      (profilePrimalCenterVariance P m0 hq t
          (fun a ↦ a.subSkew h0 h0.property) pMinus qMinus ≤
            ENNReal.ofReal (diagonalWeakMetricFactor m0
                (skewBlockCongr h0 Ft) *
              diagonalWeakLoadMinus (skewBlockCongr h0 Ft) pMinus qMinus) *
              centeredHistory P Qr rhoMax q jStar t ^ Qr⁻¹ ∧
       profileAdjointCenterVariance P m0 hq t
          (fun a ↦ a.subSkew h0 h0.property) pPlus qPlus ≤
            ENNReal.ofReal (diagonalWeakMetricFactor m0
                (skewBlockCongr h0 Ft) *
              diagonalWeakLoadPlus (skewBlockCongr h0 Ft) pPlus qPlus) *
              centeredHistory P Qr rhoMax q jStar t ^ Qr⁻¹) ∧
      (profilePrimalResponseDefect P hq h0 h0.property s t pMinus qMinus =
          (1 / 2 : ℝ) * blockVecDot ((-pMinus, qMinus) : BlockVec d)
            (blockMatVecMul
              (blockSub (profileRecenteredMean P q h0 s)
                (profileRecenteredMean P q h0 t))
              ((-pMinus, qMinus) : BlockVec d)) ∧
       profileAdjointResponseDefect P hq h0 h0.property s t pPlus qPlus =
          (1 / 2 : ℝ) * blockVecDot ((-pPlus, qPlus) : BlockVec d)
            (blockMatVecMul
              (blockSub (profileRecenteredAdjointMean P q h0 s)
                (profileRecenteredAdjointMean P q h0 t))
              ((-pPlus, qPlus) : BlockVec d))) ∧
      (0 ≤ profilePrimalResponseDefect P hq h0 h0.property s t pMinus qMinus ∧
       0 ≤ profileAdjointResponseDefect P hq h0 h0.property s t pPlus qPlus) ∧
      (profilePrimalResponseDefect P hq h0 h0.property s t pMinus qMinus ≤
          (1 / 2 : ℝ) *
            diagonalWeakLoadMinus (profileRecenteredMean P q h0 t)
              pMinus qMinus ^ 2 *
            (3 : ℝ) ^ (alpha * ((H : ℝ) - 1) / Qr) *
            (nonlinearHistory P Qr alpha q jStar t ^ Qr⁻¹).toReal ∧
       profileAdjointResponseDefect P hq h0 h0.property s t pPlus qPlus ≤
          (1 / 2 : ℝ) *
            diagonalWeakLoadPlus (profileRecenteredMean P q h0 t)
              pPlus qPlus ^ 2 *
            (3 : ℝ) ^ (alpha * ((H : ℝ) - 1) / Qr) *
            (nonlinearHistory P Qr alpha q jStar t ^ Qr⁻¹).toReal) ∧
      ((ENNReal.ofReal (profileSchurLoad (profileRecenteredMean P q h0 s)
              Xminus.1 Xminus.2) ≤
            profilePrimalHattedEarlierRow P q h0 s Xminus.1 Xminus.2 ∧
         profilePrimalHattedEarlierRow P q h0 s Xminus.1 Xminus.2 ≤
            ENNReal.ofReal (2 * profileRowGamma P rhoDr q Csrc g E
              jStar m0 s * profileQuadraticLoad
                (profileRecenteredMean P q h0 s) Xminus.1 Xminus.2)) ∧
       (ENNReal.ofReal (profileSchurLoad
              (profileRecenteredAdjointMean P q h0 s) Xplus.1 Xplus.2) ≤
            profileAdjointHattedEarlierRow P q h0 s Xplus.1 Xplus.2 ∧
         profileAdjointHattedEarlierRow P q h0 s Xplus.1 Xplus.2 ≤
            ENNReal.ofReal (2 * profileRowGamma P rhoDr q Csrc g E
              jStar m0 s * profileQuadraticLoad
                (profileRecenteredAdjointMean P q h0 s) Xplus.1 Xplus.2))) ∧
      profilePrimalSameCellMismatch P hq t h0 h0.property pMinus qMinus = 0 ∧
      profileAdjointSameCellMismatch P hq t h0 h0.property pPlus qPlus = 0 := by
  refine ⟨16, by norm_num, ?_⟩
  intro Q _hQeven hQnat P hP g hg E Psi K S Csrc hstat _hrange hdag
    hCsrc jStar M _hwindow Y hY _hYone hYmean hYnorm rhoMax hrhoSource
    hrhoMax _hexponent E0 m0 q hE0symm hE0pd hm0eq hqeq hgrid
    s t H hjs ht hH _hHt hcells hbelow
    hfin hmean hfields Cport _hCport _hportable h0 pMinus qMinus pPlus qPlus
  dsimp only
  letI : IsProbabilityMeasure P := hP
  haveI : NeZero d := ⟨by omega⟩
  have hQ : (2 : ℝ) < (Q : ℝ) := by exact_mod_cast hQnat
  have hQtwo : (2 : ℝ) ≤ (Q : ℝ) := hQ.le
  have hQone : (1 : ℝ) ≤ (Q : ℝ) := by linarith only [hQ]
  have hst : s ≤ t := by omega
  have hjt : jStar ≤ t := hjs.trans hst
  have hstart : jStar ≤ t - (H : ℤ) := by omega
  have hm0 : m0.PosDef := by
    subst m0
    exact posDef_canonMetric (posDef_toFullBlockMat hE0symm hE0pd)
  have hbelowT : ∀ k : ℤ, k < jStar → ∀ z ∈ containedCenters q k t,
      adaptedCellTranslate q k z ⊆ centeredCube d M := by
    intro k hk z hz
    exact hbelow k hk t (Or.inr rfl) z hz
  have hqpd : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hEt : BlockPosDef (adaptedMean P q t) := (hfin t hjt le_rfl).2
  have hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)) := by
    intro r hjr hrt
    exact Recurrence.adaptedMean_le hstat hgrid (by omega) (by omega)
      (hfin (r - 1) (by omega) (by omega)).1 (hfin r (by omega) hrt).1
  have halpha : (1 - g) / 4 = (1 - (1 + g) / 2) / 2 := by ring
  have hrhoWn0 : 0 < (1 + g) / 2 := by linarith only [hg.1]
  have hrhoWn1 : (1 + g) / 2 < 1 := by linarith only [hg.2]
  have hrhoDr0 : 0 ≤ ((1 - g) / 4) / 2 := by linarith only [hg.2]
  have hrhoDrWn : ((1 - g) / 4) / 2 ≤ (1 + g) / 2 := by
    linarith only [hg.1]
  have hweakSpec : (1 / 2 : ℝ) - ((1 + g) / 2) / 2 = (1 - g) / 4 := by ring
  have hrhoDrLt : ((1 - g) / 4) / 2 < (3 : ℝ) / 2 := by
    linarith only [hg.1]
  have hsource := profileSourceMoment_le hCsrc hg.2 hdag.refBlock_isSymm
    hdag.refBlock_posDef hY hm0 hqeq hgrid hjt (hcells t hjt le_rfl)
    hbelowT hrhoSource hYmean hYnorm
  have hpoint := diagonalWeakMaximum_subSkew_le_profileTotalMaximum_add_drift
    hrhoMax.le hrhoDr0 hrhoDrWn hqpd hEt hmono h0 h0.property
  have hmaxTot := eLpNorm_diagonalWeakMaximum_subSkew_le_profile hQone
    hrhoMax.le hrhoDr0 hrhoDrWn hqpd hjt hEt hmono h0 h0.property
  have hmaxSplit :=
    eLpNorm_diagonalWeakMaximum_subSkew_le_centered_source_drift hQone
      hrhoMax.le hrhoDr0 hrhoDrWn hqpd hjt hEt hmono h0 h0.property
  have hminkowski := profileTotalHistory_rpow_inv_le (rhoMax := rhoMax)
    hQone hqpd hjt hEt
    (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt
  have hcell := eLpNorm_diagonalWeakCellSum_subSkew_le_profile
    (alpha := (1 - g) / 4) hqpd hQtwo (le_trans hg.1 hrhoSource.le)
    hstat hgrid le_rfl (fun k hjk hkt ↦ (hfin k hjk hkt).1) hstart hEt
    hmean h0 h0.property
  have hav := eLpNorm_diagonalWeakAverageSum_subSkew_le_profile hqpd
    hQone hweakSpec hstat hgrid le_rfl
    (fun k hjk hkt ↦ (hfin k hjk hkt).1) hstart h0 h0.property
  have henergyMinus := profileEnergy_subSkew_le_of_window
    (H := H) (alpha := (1 - g) / 4) hCsrc hg.2
    hdag.refBlock_isSymm hdag.refBlock_posDef hY hm0 hqeq hgrid hjt hQ
    hrhoSource hrhoMax.le hrhoDr0 hrhoDrWn hstat hcells hbelowT hfin
    hYmean hYnorm h0 h0.property pMinus qMinus
  have henergyPlus := profileEnergy_subSkew_le_of_window
    (H := H) (alpha := (1 - g) / 4) hCsrc hg.2
    hdag.refBlock_isSymm hdag.refBlock_posDef hY hm0 hqeq hgrid hjt hQ
    hrhoSource hrhoMax.le hrhoDr0 hrhoDrWn hstat hcells hbelowT hfin
    hYmean hYnorm h0 h0.property pPlus qPlus
  have hweak := eLpNorm_profileWeakRoots_subSkew_le hCsrc hg.2
    hdag.refBlock_isSymm hdag.refBlock_posDef hY hm0 hqeq hgrid
    (fun k hjk hkt ↦ (hfin k hjk hkt).1) hstart (hcells t hjt le_rfl)
    hbelowT (by positivity) hrhoSource hYmean hYnorm hrhoMax.le hrhoDr0
    hrhoDrWn hmono hstat hm0 hrhoWn0 hrhoWn1 halpha h0 h0.property
    pMinus qMinus pPlus qPlus
  have hcenMinus := profilePrimalCenterVariance_subSkew_le
    (rhoMax := rhoMax) hQtwo hm0 hqpd hjt (hfin t hjt le_rfl).1 hEt
    h0 h0.property pMinus qMinus
  have hcenPlus := profileAdjointCenterVariance_subSkew_le
    (rhoMax := rhoMax) hQtwo hm0 hqpd hjt (hfin t hjt le_rfl).1 hEt
    h0 h0.property pPlus qPlus
  have hidMinus := profilePrimalResponseDefect_identity hqpd h0.property
    (hfin s hjs hst).1 (hfin t hjt le_rfl).1 pMinus qMinus
  have hidPlus := profileAdjointResponseDefect_identity hqpd h0.property
    (hfin s hjs hst).1 (hfin t hjt le_rfl).1 pPlus qPlus
  have hnonnegMinus := profilePrimalResponseDefect_nonneg hqpd h0.property
    (hfin s hjs hst).1 (hfin t hjt le_rfl).1 (hmean s hjs hst)
    pMinus qMinus
  have hnonnegPlus := profileAdjointResponseDefect_nonneg hqpd h0.property
    (hfin s hjs hst).1 (hfin t hjt le_rfl).1 (hmean s hjs hst)
    pPlus qPlus
  have hdefMinus := profilePrimalResponseDefect_le_nonlinearHistory
    (a := (1 - g) / 4) h0.property hQone hstat hgrid le_rfl
    (fun k hjk hkt ↦ (hfin k hjk hkt).1) hjs ht hH pMinus qMinus
  have hdefPlus := profileAdjointResponseDefect_le_nonlinearHistory
    (a := (1 - g) / 4) h0.property hQone hstat hgrid le_rfl
    (fun k hjk hkt ↦ (hfin k hjk hkt).1) hjs ht hH pPlus qPlus
  have hrows := profileAllEarlierRows (rhoDr := ((1 - g) / 4) / 2)
    hstat hY (lt_of_lt_of_le zero_lt_one hCsrc) hg.2 hm0
    (by rw [← hqeq]; exact hgrid) hrhoDrLt hjs
    (by rw [← hqeq]; exact hcells s hjs hst)
    (fun k hjk hks ↦ by rw [← hqeq]; exact (hfin k hjk (hks.trans hst)).1)
    hfields h0
    (profilePrimalCenter P hqpd t (fun a ↦ a.subSkew h0 h0.property)
      pMinus qMinus).1
    (profilePrimalCenter P hqpd t (fun a ↦ a.subSkew h0 h0.property)
      pMinus qMinus).2
    (profileAdjointCenter P hqpd t (fun a ↦ a.subSkew h0 h0.property)
      pPlus qPlus).1
    (profileAdjointCenter P hqpd t (fun a ↦ a.subSkew h0 h0.property)
      pPlus qPlus).2
  rw [← hqeq] at hrows
  have hmismatch := profileSameCellMismatches_eq_zero P hqpd t h0
    h0.property pMinus qMinus pPlus qPlus
  refine ⟨hsource, ⟨hpoint, hmaxTot, hminkowski, hmaxSplit⟩, hcell, hav,
    ⟨henergyMinus.1, henergyPlus.2.1, henergyMinus.2.2.1,
      henergyPlus.2.2.2⟩,
    hweak.1, hweak.2, ⟨hcenMinus, hcenPlus⟩, ⟨hidMinus, hidPlus⟩,
    ⟨hnonnegMinus, hnonnegPlus⟩, ⟨hdefMinus, hdefPlus⟩, hrows,
    hmismatch.1, hmismatch.2⟩

end

end Homogenization.HighContrast.Response
