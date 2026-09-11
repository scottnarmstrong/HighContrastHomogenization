/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileCarriers
import HCPoly.Provider.Response.SourceBuffer
import HCPoly.Provider.Transport.WindowBelowStart
import HCPoly.Provider.Transport.WindowTerminalNormalization

/-!
# The below-start source moment

The common window multiplier controls every cell below the alignment on one
event.  Its `L^Q` cap and its mean cap then give the coefficient
`4 κ_E B_q²` in the bound for the moment of the below-start source maximum.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The below-start moment is bounded by the capped source contribution.  The
spatial metric is tied to the rounded grid by the displayed equality; the
additional rounded-grid witness records the geometry used by the cell API. -/
theorem profileSourceMoment_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Q rhoMax Cd : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {jStar M t : ℤ} {Y : CoeffSpace d → ℝ}
    (hCd : 1 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef)
    (hqeq : q = roundedGrid jStar m0) (hgrid : IsRoundedGrid jStar q)
    (hjt : jStar ≤ t)
    (hcell : adaptedCell q t ⊆ centeredCube d M)
    (hbelow : ∀ k : ℤ, k < jStar → ∀ z ∈ containedCenters q k t,
      adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hrho : g < rhoMax)
    (hYmean : ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y)
    (hYnorm : lqNorm P Q Y ≤ 2) :
    profileSourceMoment P Q rhoMax q jStar t (adaptedMean P q t) ≤
      ENNReal.ofReal
        (4 * kappaRef E * boundaryConst Cd g m0 ^ 2 *
          (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ)))) := by
  subst q
  have hCd0 : 0 < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hB0 : 0 ≤ boundaryConst Cd g m0 :=
    Transport.zero_le_boundaryConst (le_trans zero_le_one hCd) hg m0
  have hBpos : 0 < boundaryConst Cd g m0 :=
    Transport.zero_lt_boundaryConst hCd0 hg hm0
  have hFsym : IsSymmetricBlockMat
      (adaptedMean P (roundedGrid jStar m0) t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar m0) t
  have hFpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar m0) t) :=
    Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hm0 hgrid hjt hcell
  have hmain := Transport.eLpNorm_belowStartSup_le
    (le_trans zero_le_one hCd) hg hE hEpd hY hm0 hgrid hFsym hFpd hrho t
      hbelow Q
  have hsize := Transport.blockSize_adaptedMean_le
    hCd0 hg hE hEpd hY hm0 hgrid hjt hcell
  have hEY2 : (∫ a, Y a ∂P) ≤ 2 := integral_le_two hYmean hYnorm
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_blockSharp hE hEpd
  have hsharpPd : Book.Ch02.BlockPosDef (blockSharp E) := by
    refine (blockPosDef_iff_posDef hsharpSymm).mpr ?_
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp (posDef_toFullBlockMat hE hEpd)
  have hkappa0 : 0 ≤ kappaRef E :=
    PortableHistory.blockSize_nonneg hE hsharpSymm hsharpPd
  have hsize2 :
      blockSize E (adaptedMean P (roundedGrid jStar m0) t) ≤
        kappaRef E * (boundaryConst Cd g m0 * 2) := by
    refine hsize.trans ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hEY2 hB0) hkappa0
  have hpow : 0 <
      (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) := by
    positivity
  have hreal :
      boundaryConst Cd g m0 *
            blockSize E (adaptedMean P (roundedGrid jStar m0) t) *
            (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) * 2 ≤
        4 * kappaRef E * boundaryConst Cd g m0 ^ 2 *
          (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) := by
    have h1 := mul_le_mul_of_nonneg_left hsize2 hB0
    have h2 := mul_le_mul_of_nonneg_right h1 hpow.le
    have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 2)
    calc
      boundaryConst Cd g m0 *
            blockSize E (adaptedMean P (roundedGrid jStar m0) t) *
            (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) * 2
          ≤ boundaryConst Cd g m0 *
              (kappaRef E * (boundaryConst Cd g m0 * 2)) *
              (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) * 2 := h3
      _ = 4 * kappaRef E * boundaryConst Cd g m0 ^ 2 *
            (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) := by ring
  have hc0 : 0 ≤
      boundaryConst Cd g m0 *
        blockSize E (adaptedMean P (roundedGrid jStar m0) t) *
        (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) := by
    exact mul_nonneg
      (mul_nonneg hB0 (PortableHistory.blockSize_nonneg hE hFsym hFpd)) hpow.le
  change eLpNorm
      (belowStartSup rhoMax (roundedGrid jStar m0) jStar t
        (fun k ↦ containedCenters (roundedGrid jStar m0) k t)
        (adaptedMean P (roundedGrid jStar m0) t))
      (ENNReal.ofReal Q) P ≤ _
  calc
    eLpNorm
          (belowStartSup rhoMax (roundedGrid jStar m0) jStar t
            (fun k ↦ containedCenters (roundedGrid jStar m0) k t)
            (adaptedMean P (roundedGrid jStar m0) t))
          (ENNReal.ofReal Q) P
        ≤ ENNReal.ofReal
              (boundaryConst Cd g m0 *
                blockSize E (adaptedMean P (roundedGrid jStar m0) t) *
                (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ)))) *
            lqNorm P Q Y := hmain
    _ ≤ ENNReal.ofReal
              (boundaryConst Cd g m0 *
                blockSize E (adaptedMean P (roundedGrid jStar m0) t) *
                (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ)))) *
            ENNReal.ofReal 2 := by
          exact mul_le_mul_right
            (hYnorm.trans_eq (by norm_num : (2 : ℝ≥0∞) = ENNReal.ofReal 2)) _
    _ = ENNReal.ofReal
          (boundaryConst Cd g m0 *
            blockSize E (adaptedMean P (roundedGrid jStar m0) t) *
            (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ))) * 2) := by
          rw [← ENNReal.ofReal_mul hc0]
    _ ≤ ENNReal.ofReal
          (4 * kappaRef E * boundaryConst Cd g m0 ^ 2 *
            (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (jStar : ℝ)))) :=
      ENNReal.ofReal_le_ofReal hreal

end

end Homogenization.HighContrast.Response
