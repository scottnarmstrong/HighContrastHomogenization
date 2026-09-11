/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CommonQuantitativeAffineScale

/-!
# Quantitative certificates at the common affine scale

The common R1-A/R3-A enlargement preserves the same normalized reference
family, response order, target amplitude, and decay exponent.  This is the
certificate-level bridge needed before the physical regularity providers use
the single enlarged scale.
-/

namespace Homogenization
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- Moving the effective start to a later positive scale preserves a
quantitative normalized reference certificate at the same amplitude. -/
theorem QuantitativeNormalizedReferenceCertificate.enlargeScale
    [NeZero d] {abar : Mat d} {a : CoeffSpace d}
    {x y s amplitude kappa : ℝ}
    (h : QuantitativeNormalizedReferenceCertificate
      abar s amplitude kappa x a)
    (hy : 0 < y) (hxy : x ≤ y) :
    QuantitativeNormalizedReferenceCertificate
      abar s amplitude kappa y a := by
  obtain ⟨hS, aRef, hs, hsLt, hAmplitude, hKappa, hx, haRef, htail⟩ := h
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  refine ⟨hS, aRef, hs, hsLt, hAmplitude, hKappa, hx.trans hxy, haRef, ?_⟩
  intro k hyk
  have hxk : x ≤ (3 : ℝ) ^ k := hxy.trans hyk
  have hPow : 0 < (3 : ℝ) ^ k := by positivity
  have hRatio : (3 : ℝ) ^ k / y ≤ (3 : ℝ) ^ k / x :=
    div_le_div_of_nonneg_left hPow.le hxPos hxy
  have hDecay :
      (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
        (((3 : ℝ) ^ k) / y) ^ (-kappa) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hPow hy) hRatio
      (neg_nonpos.mpr hKappa.le)
  exact (htail k hxk).trans
    (mul_le_mul_of_nonneg_left hDecay hAmplitude)

/-- First reduce the retained R1-A amplitude to a positive target, then insert
the R3-A rounded-affine multiplier exactly once.  The resulting common scale
carries that same target certificate. -/
theorem QuantitativeNormalizedReferenceCertificate.commonAffineScale
    [NeZero d] {abar : Mat d} {a : CoeffSpace d}
    {s amplitude target kappaRate Caff overlinePi kappaCube : ℝ}
    {X : CoeffSpace d → ℝ}
    (h : QuantitativeNormalizedReferenceCertificate
      abar s amplitude kappaRate (X a) a)
    (hTarget : 0 < target) :
    QuantitativeNormalizedReferenceCertificate abar s target kappaRate
      (commonQuantitativeAffineScale amplitude target kappaRate Caff
        overlinePi kappaCube X a) a := by
  have hTargeted := h.targetedEffectiveScale hTarget
  have hTargetedData := hTargeted
  obtain ⟨_, _, _, _, _, _, hRateOne, _, _⟩ := hTargetedData
  have hRateNonneg : 0 ≤ targetedQuantitativeEffectiveScale
      amplitude target kappaRate X a := zero_le_one.trans hRateOne
  have hCommonPos : 0 < roundedAffineEffectiveScale Caff overlinePi kappaCube
      (targetedQuantitativeEffectiveScale amplitude target kappaRate X a) :=
    zero_lt_one.trans_le
      (one_le_roundedAffineEffectiveScale Caff overlinePi kappaCube _ hRateOne)
  have hRateCommon : targetedQuantitativeEffectiveScale
      amplitude target kappaRate X a ≤
        roundedAffineEffectiveScale Caff overlinePi kappaCube
          (targetedQuantitativeEffectiveScale amplitude target kappaRate X a) :=
    le_roundedAffineEffectiveScale Caff overlinePi kappaCube _ hRateNonneg
  simpa only [commonQuantitativeAffineScale] using
    hTargeted.enlargeScale hCommonPos hRateCommon

end

end HighContrast
end Homogenization
