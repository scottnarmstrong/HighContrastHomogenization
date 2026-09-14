/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.ProviderMonotonicity
import HCPoly.Provider.ShortHop.SourceCoefficient

/-!
# Upward closure of the two-grid bridge constant

The comparison and shifted-drift estimates remain valid when their common
constant is increased, provided the scale tests are imposed with the larger
constant.  In particular, independently supplied transport and bridge
constants may be replaced by one common maximum.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

private theorem blockScale_mono_of_full_posDef {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {a b : ℝ} (hab : a ≤ b) :
    BlockMatLoewnerLE (blockScale a E) (blockScale b E) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale, toFullBlockMat_blockScale]
  refine Matrix.le_iff.mpr ?_
  have hps := hE.posSemidef.smul (sub_nonneg.mpr hab)
  simpa [sub_smul] using hps

private theorem bridgeCmpRemainder_mono_constant {C C' Cd g rhoDr : ℝ}
    (hCC' : C ≤ C') (hCd : 0 ≤ Cd) (hg : g < 1) (E : BlockMat d)
    {jStar v : ℤ} (hv : jStar ≤ v) (mq mq' : Mat d) :
    bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' v ≤
      bridgeCmpRemainder C' Cd g rhoDr E jStar mq mq' v := by
  have hsrc : 0 ≤ bridgeSrcCoeff Cd g E jStar mq mq' :=
    zero_le_one.trans (ShortHop.one_le_bridgeSrcCoeff hCd hg E jStar mq mq')
  have hlin : 0 ≤ 1 + ((v : ℝ) - (jStar : ℝ)) := by
    have hv' : (jStar : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    linarith only [hv']
  have htail : 0 ≤ (1 + ((v : ℝ) - (jStar : ℝ))) *
      (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (jStar : ℝ))) :=
    mul_nonneg hlin (by positivity)
  have hfront : C * bridgeSrcCoeff Cd g E jStar mq mq' ≤
      C' * bridgeSrcCoeff Cd g E jStar mq mq' :=
    mul_le_mul_of_nonneg_right hCC' hsrc
  simpa only [bridgeCmpRemainder, mul_assoc] using
    mul_le_mul_of_nonneg_right hfront htail

private theorem bridgeShiftedRemainder_mono_constant {C C' Cd g rhoDr : ℝ}
    (hCC' : C ≤ C') (hCd : 0 ≤ Cd) (hg : g < 1) (E : BlockMat d)
    {jStar n : ℤ} (hn : jStar ≤ n) (mq mq' : Mat d) (l : ℤ) :
    bridgeShiftedRemainder C Cd g rhoDr E jStar mq mq' n l ≤
      bridgeShiftedRemainder C' Cd g rhoDr E jStar mq mq' n l := by
  have hsrc : 0 ≤ bridgeSrcCoeff Cd g E jStar mq mq' :=
    zero_le_one.trans (ShortHop.one_le_bridgeSrcCoeff hCd hg E jStar mq mq')
  have hlin : 0 ≤ 1 + ((n : ℝ) - (jStar : ℝ)) := by
    have hn' : (jStar : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith only [hn']
  have htail : 0 ≤ (3 : ℝ) ^ (rhoDr * (l : ℝ)) *
      (1 + ((n : ℝ) - (jStar : ℝ))) *
        (3 : ℝ) ^ (-rhoDr * ((n : ℝ) - (jStar : ℝ))) :=
    mul_nonneg (mul_nonneg (by positivity) hlin) (by positivity)
  have hfront : C * bridgeSrcCoeff Cd g E jStar mq mq' ≤
      C' * bridgeSrcCoeff Cd g E jStar mq mq' :=
    mul_le_mul_of_nonneg_right hCC' hsrc
  simpa only [bridgeShiftedRemainder, mul_assoc] using
    mul_le_mul_of_nonneg_right hfront htail

/-- The exact two-grid comparison and shifted-drift conclusion is preserved
when its constant is enlarged and its two scale gates use the larger value. -/
theorem twoGridShiftedDrift_enlargeConstant (hd : 2 ≤ d)
    {C C' Cd g Q Klaw : ℝ} (hC : 0 < C) (hCC' : C ≤ C')
    (hCd : 0 ≤ Cd) (hg : g < 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {E : BlockMat d} {Psi : ℝ → ℝ} {jStar M : ℤ}
    (hwin : IsCoupledWindow d Q Klaw jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Psi Klaw Cd jStar M Y)
    (raw : ∀ mp mv : Mat d, mp.PosDef → mv.PosDef →
      ∀ nn l : ℤ, jStar ≤ nn - l →
      C * (1 + Real.log (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))) ≤
          (l : ℝ) →
      C * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
          (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
      (∀ r : Mat d, r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
          adaptedCell r j ⊆ centeredCube d M) →
      BlockMatLoewnerLE
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn - l)))
          (blockScale (bridgeErrUpper C Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) nn)) ∧
        BlockMatLoewnerLE
          (blockScale (-bridgeErrLower C Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn + l))) ∧
        ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
          BlockMatLoewnerLE
            (blockScale (1 - eta) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
            (adaptedMean P (roundedGrid jStar mv) nn) →
          linearDrift P (initExpRhoDr g) (roundedGrid jStar mv) jStar nn ≤
            C * (eta + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
              (3 : ℝ) ^ (-(l : ℝ)) +
              (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
                (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) +
              bridgeShiftedRemainder C Cd g (initExpRhoDr g) E jStar mp mv nn l)) :
    ∀ mp mv : Mat d, mp.PosDef → mv.PosDef →
      ∀ nn l : ℤ, jStar ≤ nn - l →
      C' * (1 + Real.log (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))) ≤
          (l : ℝ) →
      C' * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
          (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
      (∀ r : Mat d, r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
          adaptedCell r j ⊆ centeredCube d M) →
      BlockMatLoewnerLE
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn - l)))
          (blockScale (bridgeErrUpper C' Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) nn)) ∧
        BlockMatLoewnerLE
          (blockScale (-bridgeErrLower C' Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn + l))) ∧
        ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
          BlockMatLoewnerLE
            (blockScale (1 - eta) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
            (adaptedMean P (roundedGrid jStar mv) nn) →
          linearDrift P (initExpRhoDr g) (roundedGrid jStar mv) jStar nn ≤
            C' * (eta + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
              (3 : ℝ) ^ (-(l : ℝ)) +
              (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
                (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) +
              bridgeShiftedRemainder C' Cd g (initExpRhoDr g) E jStar mp mv nn l) := by
  let : NeZero d := ⟨by omega⟩
  intro mp mv hmp hmv nn l hj hscale hsmall hcont
  let K : ℝ := gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)
  have hK : 1 ≤ K := Transport.one_le_gridRatio _ _
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have honeLog : 0 ≤ 1 + Real.log K := by linarith only [hlog]
  have hscaleOld : C * (1 + Real.log K) ≤ (l : ℝ) :=
    (mul_le_mul_of_nonneg_right hCC' honeLog).trans hscale
  have hpow : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) := by positivity
  have hKpow : 0 ≤ K * (3 : ℝ) ^ (-(l : ℝ)) := mul_nonneg hK0 hpow
  have hsmallOld : C * K * (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 := by
    calc
      C * K * (3 : ℝ) ^ (-(l : ℝ)) = C * (K * (3 : ℝ) ^ (-(l : ℝ))) := by ring
      _ ≤ C' * (K * (3 : ℝ) ^ (-(l : ℝ))) :=
        mul_le_mul_of_nonneg_right hCC' hKpow
      _ = C' * K * (3 : ℝ) ^ (-(l : ℝ)) := by ring
      _ ≤ 1 / 2 := hsmall
  obtain ⟨hupper, hlower, hshift⟩ :=
    raw mp mv hmp hmv nn l hj hscaleOld hsmallOld hcont
  have hC' : 0 < C' := hC.trans_le hCC'
  have hweightOne : 1 ≤ 1 + Real.log K := by linarith only [hlog]
  have hCmul : C' ≤ C' * (1 + Real.log K) := by
    simpa using mul_le_mul_of_nonneg_left hweightOne hC'.le
  have hCl : C' ≤ (l : ℝ) := hCmul.trans hscale
  have hlReal : 0 < (l : ℝ) := hC'.trans_le hCl
  have hl : (0 : ℤ) < l := by exact_mod_cast hlReal
  have hjnn : jStar ≤ nn := by omega
  have hjterm : jStar ≤ nn + l := by omega
  have hcontOld : ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
      adaptedCell (roundedGrid jStar mp) j ⊆ centeredCube d M :=
    fun j hjs hjtop => hcont _ (Or.inl rfl) j hjs hjtop
  have hEn : (toFullBlockMat (adaptedMean P (roundedGrid jStar mp) nn)).PosDef :=
    ShortHop.posDef_adaptedMean_of_window hwin hY hmp hjnn (by omega) hcontOld
  have hEt : (toFullBlockMat
      (adaptedMean P (roundedGrid jStar mp) (nn + l))).PosDef :=
    ShortHop.posDef_adaptedMean_of_window hwin hY hmp hjterm le_rfl hcontOld
  have hDnn : 0 ≤ linearDrift P (initExpRhoDr g)
      (roundedGrid jStar mp) jStar nn :=
    ShortHop.linearDrift_nonneg_of_window hstat hwin hY hmp hjnn (by omega) hcontOld
  have hDterm : 0 ≤ linearDrift P (initExpRhoDr g)
      (roundedGrid jStar mp) jStar (nn + l) :=
    ShortHop.linearDrift_nonneg_of_window hstat hwin hY hmp hjterm le_rfl hcontOld
  have hbrUpper : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) +
      (3 : ℝ) ^ (-(1 - initExpRhoDr g) * (l : ℝ)) *
        linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar nn :=
    add_nonneg hpow (mul_nonneg (by positivity) hDnn)
  have hremUpper := bridgeCmpRemainder_mono_constant (rhoDr := initExpRhoDr g)
    hCC' hCd hg E hjnn mp mv
  have herrUpper : bridgeErrUpper C Cd g (initExpRhoDr g) K P E jStar mp mv nn l ≤
      bridgeErrUpper C' Cd g (initExpRhoDr g) K P E jStar mp mv nn l := by
    rw [bridgeErrUpper, bridgeErrUpper]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hK0) hbrUpper)
      hremUpper
  refine ⟨hupper.trans (blockScale_mono_of_full_posDef hEn herrUpper), ?_, ?_⟩
  have hnum : C * K ≤ C' * K := mul_le_mul_of_nonneg_right hCC' hK0
  have hden' : 0 < 1 - C' * K * (3 : ℝ) ^ (-(l : ℝ)) := by
    linarith only [hsmall]
  have hdenOrder : 1 - C' * K * (3 : ℝ) ^ (-(l : ℝ)) ≤
      1 - C * K * (3 : ℝ) ^ (-(l : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hnum hpow
    linarith only [hm]
  have hcoef : C * K / (1 - C * K * (3 : ℝ) ^ (-(l : ℝ))) ≤
      C' * K / (1 - C' * K * (3 : ℝ) ^ (-(l : ℝ))) :=
    div_le_div₀ (mul_nonneg hC'.le hK0) hnum hden' hdenOrder
  have hden : 0 < 1 - C * K * (3 : ℝ) ^ (-(l : ℝ)) := hden'.trans_le hdenOrder
  have hcoef0 : 0 ≤ C * K / (1 - C * K * (3 : ℝ) ^ (-(l : ℝ))) :=
    div_nonneg (mul_nonneg hC.le hK0) hden.le
  have hbrLower : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) +
      (3 : ℝ) ^ (-(1 - initExpRhoDr g) * (l : ℝ)) *
        linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) :=
    add_nonneg hpow (mul_nonneg (by positivity) hDterm)
  have hremLower := bridgeCmpRemainder_mono_constant (rhoDr := initExpRhoDr g)
    hCC' hCd hg E hjterm mv mp
  have herrLower : bridgeErrLower C Cd g (initExpRhoDr g) K P E jStar mp mv nn l ≤
      bridgeErrLower C' Cd g (initExpRhoDr g) K P E jStar mp mv nn l := by
    rw [bridgeErrLower, bridgeErrLower]
    exact add_le_add (mul_le_mul_of_nonneg_right hcoef hbrLower) hremLower
  · exact (blockScale_mono_of_full_posDef hEt (neg_le_neg herrLower)).trans hlower
  · intro eta heta heta4 hnear
    have hdrift := hshift eta heta heta4 hnear
    have hremShift := bridgeShiftedRemainder_mono_constant (rhoDr := initExpRhoDr g)
      hCC' hCd hg E hjnn mp mv l
    have hterm : 0 ≤ (1 + K) * (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
        linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) :=
      mul_nonneg (mul_nonneg (by linarith only [hK]) (by positivity)) hDterm
    have hbase : 0 ≤ eta + K * (3 : ℝ) ^ (-(l : ℝ)) +
        (1 + K) * (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
          linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) :=
      add_nonneg (add_nonneg heta hKpow) hterm
    have hremShift' : 0 ≤ bridgeShiftedRemainder C' Cd g (initExpRhoDr g)
        E jStar mp mv nn l := ShortHop.zero_le_bridgeShiftedRemainder hC'.le hCd hg E hjnn mp mv l
    have hinner :
        eta + K * (3 : ℝ) ^ (-(l : ℝ)) +
              (1 + K) * (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) +
              bridgeShiftedRemainder C Cd g (initExpRhoDr g) E jStar mp mv nn l ≤
          eta + K * (3 : ℝ) ^ (-(l : ℝ)) +
              (1 + K) * (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) +
              bridgeShiftedRemainder C' Cd g (initExpRhoDr g) E jStar mp mv nn l :=
      add_le_add_right hremShift _
    have hfirst := mul_le_mul_of_nonneg_left hinner hC.le
    have hsecond := mul_le_mul_of_nonneg_right hCC'
      (add_nonneg hbase hremShift')
    exact hdrift.trans (hfirst.trans hsecond)

end

end Homogenization.HighContrast.Selection
