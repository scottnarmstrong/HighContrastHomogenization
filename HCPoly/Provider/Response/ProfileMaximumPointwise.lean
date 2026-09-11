/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileMaximumMean
import HCPoly.Provider.Response.DiagonalWeakNormMaximum

/-!
# The complete terminal maximum, pointwise

The all-scale maximum is split at the alignment.  Earlier cells are terms of
the common source maximum.  Retained cells are split at their own annealed
mean; their centered parts enter the centered maximum and their mean parts
enter the fixed-grid drift.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Above the alignment, one weighted all-scale excess is controlled by the
centered maximum and the terminal drift. -/
theorem ofReal_retained_excess_le_profile_add_drift [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax rhoDr rhoWn : ℝ}
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn) {q : Mat d} (hq : q.PosDef)
    {jStar k t : ℤ} (hjk : jStar ≤ k) (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)))
    (a : CoeffSpace d) :
    ENNReal.ofReal
        ((3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) *
          blockExcess (adaptedResponse q k w a) (adaptedMean P q t)) ≤
      profileCenteredMaximum P rhoMax q jStar t a +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) := by
  let A := adaptedResponse q k w a
  let Ek := adaptedMean P q k
  let Et := adaptedMean P q t
  let wWn : ℝ := (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ)))
  let wMax : ℝ := (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ)))
  have hAs : IsSymmetricBlockMat A :=
    Recurrence.isSymmetricBlockMat_adaptedResponse q k w a
  have hApsd : (toFullBlockMat A).PosSemidef :=
    (posDef_toFullBlockMat hAs
      (Recurrence.blockPosDef_adaptedResponse hq k w a)).posSemidef
  have hEks : IsSymmetricBlockMat Ek :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q k
  have hEts : IsSymmetricBlockMat Et :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hcenter0 : 0 ≤ blockSize (blockSub A Ek) Et :=
    PortableHistory.blockSize_nonneg (isSymmetricBlockMat_blockSub hAs hEks) hEts hEt
  have hmean0 : 0 ≤ blockSize (blockSub Ek Et) Et :=
    PortableHistory.blockSize_nonneg (isSymmetricBlockMat_blockSub hEks hEts) hEts hEt
  have hwWn0 : 0 ≤ wWn := Real.rpow_nonneg (by norm_num) _
  have hwMax0 : 0 ≤ wMax := Real.rpow_nonneg (by norm_num) _
  have hgap : (0 : ℝ) ≤ (t : ℝ) - (k : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hkt
  have hweights : wWn ≤ wMax := by
    dsimp only [wWn, wMax]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have := mul_le_mul_of_nonneg_right hrhoMax hgap
    linarith only [this]
  have hsplit : blockExcess A Et ≤
      blockSize (blockSub A Ek) Et + blockSize (blockSub Ek Et) Et :=
    (blockExcess_le_blockSize_blockSub hAs hApsd hEts hEt).trans
      (blockSize_blockSub_triangle hAs hEks hEts hEts hEt)
  have hreal : wWn * blockExcess A Et ≤
      wMax * blockSize (blockSub A Ek) Et +
        wWn * blockSize (blockSub Ek Et) Et := by
    calc
      wWn * blockExcess A Et ≤
          wWn * (blockSize (blockSub A Ek) Et +
            blockSize (blockSub Ek Et) Et) :=
        mul_le_mul_of_nonneg_left hsplit hwWn0
      _ = wWn * blockSize (blockSub A Ek) Et +
          wWn * blockSize (blockSub Ek Et) Et := by ring
      _ ≤ wMax * blockSize (blockSub A Ek) Et +
          wWn * blockSize (blockSub Ek Et) Et := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hweights hcenter0) le_rfl
  have hcenter : ENNReal.ofReal
      (wMax * blockSize (blockSub A Ek) Et) ≤
      profileCenteredMaximum P rhoMax q jStar t a := by
    dsimp only [wMax, A, Ek, Et]
    exact ofReal_centered_cell_le_profileCenteredMaximum hjk hkt
      ((mem_alignedIndex_iff hq hkt).mp hw) a
  have hmean : wWn * blockSize (blockSub Ek Et) Et ≤
      linearDrift P rhoDr q jStar t := by
    dsimp only [wWn, Ek, Et]
    exact weighted_mean_sub_le_linearDrift hrhoDr hrhoDrWn hjk hkt hEt hmono
  calc
    ENNReal.ofReal (wWn * blockExcess A Et) ≤
        ENNReal.ofReal
          (wMax * blockSize (blockSub A Ek) Et +
            wWn * blockSize (blockSub Ek Et) Et) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (wMax * blockSize (blockSub A Ek) Et) +
        ENNReal.ofReal (wWn * blockSize (blockSub Ek Et) Et) := by
      rw [ENNReal.ofReal_add (mul_nonneg hwMax0 hcenter0)
        (mul_nonneg hwWn0 hmean0)]
    _ ≤ profileCenteredMaximum P rhoMax q jStar t a +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) :=
      add_le_add hcenter (ENNReal.ofReal_le_ofReal hmean)

/-- Below the alignment, one weighted all-scale excess is a term of the common
source maximum. -/
theorem ofReal_earlier_excess_le_profileSourceMaximum [NeZero d]
    {rhoMax rhoWn : ℝ} (hrho : rhoMax ≤ rhoWn)
    {q : Mat d} (hq : q.PosDef) {jStar k t : ℤ}
    (hjk : k < jStar) (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    (a : CoeffSpace d) :
    ENNReal.ofReal
        ((3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) *
          blockExcess (adaptedResponse q k w a) F) ≤
      profileSourceMaximum rhoMax q jStar t F a := by
  let z : Vec d := adaptedCellCenter q k w
  have hz : z ∈ containedCenters q k t :=
    ⟨⟨w, rfl⟩, (mem_alignedIndex_iff hq hkt).mp hw⟩
  have hgap : (0 : ℝ) ≤ (t : ℝ) - (k : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hkt
  have hweight :
      (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) ≤
        (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have := mul_le_mul_of_nonneg_right hrho hgap
    linarith only [this]
  have hexc0 : 0 ≤ blockExcess (adaptedResponse q k w a) F := by
    have hA := Recurrence.isSymmetricBlockMat_adaptedResponse q k w a
    have hApsd := (posDef_toFullBlockMat hA
      (Recurrence.blockPosDef_adaptedResponse hq k w a)).posSemidef
    exact blockExcess_nonneg hA hApsd hF hFpd
  have hterm : ENNReal.ofReal
      ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
        blockExcess (adaptedResponse q k w a) F) ≤
      profileSourceMaximum rhoMax q jStar t F a := by
    rw [profileSourceMaximum_eq, belowStartSup]
    refine le_iSup_of_le k (le_iSup_of_le hjk
      (le_iSup_of_le z (le_iSup_of_le hz ?_)))
    change ENNReal.ofReal
        ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
          blockExcess
            (coarseBlock
              (adaptedCellTranslate q k (adaptedCellCenter q k w)) a) F) ≤ _
    exact le_rfl
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hweight hexc0)).trans hterm

/-- The complete all-scale maximum is bounded by the complete profile maximum
plus the terminal fixed-grid drift. -/
theorem diagonalWeakMaximum_le_profileTotalMaximum_add_drift [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax rhoDr rhoWn : ℝ}
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn) {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ}
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)))
    (a : CoeffSpace d) :
    diagonalWeakMaximum rhoWn q t (adaptedMean P q t) a ≤
      profileTotalMaximum P rhoMax q jStar t (adaptedMean P q t) a +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) := by
  rw [diagonalWeakMaximum_eq]
  refine iSup_le fun k => iSup_le fun hkt => iSup_le fun w => iSup_le fun hw => ?_
  by_cases hjk : jStar ≤ k
  · have h := ofReal_retained_excess_le_profile_add_drift
      hrhoMax hrhoDr hrhoDrWn hq hjk hkt hw hEt hmono a
    rw [profileTotalMaximum_eq]
    exact h.trans (add_le_add (le_add_right le_rfl) le_rfl)
  · have h := ofReal_earlier_excess_le_profileSourceMaximum
      hrhoMax hq (lt_of_not_ge hjk) hkt hw
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt a
    rw [profileTotalMaximum_eq]
    exact h.trans ((le_add_left le_rfl).trans (le_add_right le_rfl))

end

end Homogenization.HighContrast.Response
