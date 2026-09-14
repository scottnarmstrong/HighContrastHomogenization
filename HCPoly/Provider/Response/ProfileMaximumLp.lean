/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileMaximumPointwise
import HCPoly.Provider.Response.ProfileRecentCellLp
import HCPoly.Provider.Window.ScaleMeasurability
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Moments of the complete terminal maximum

The below-start maximum is rewritten over the countable aligned labels before
measurability is proved.  Minkowski then compares the complete history with
the centered history and source moment, without an independence assumption.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The center-indexed source maximum is the same supremum written over aligned
integer labels. -/
theorem profileSourceMaximum_eq_iSup_aligned [NeZero d]
    {rhoMax : ℝ} {q : Mat d} (hq : q.PosDef) {jStar t : ℤ}
    (hjt : jStar ≤ t) (F : BlockMat d) (a : CoeffSpace d) :
    profileSourceMaximum rhoMax q jStar t F a =
      ⨆ (k : ℤ) (_ : k < jStar) (w : Fin d → ℤ)
          (_ : w ∈ alignedIndex q k t),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
            blockExcess (adaptedResponse q k w a) F) := by
  rw [profileSourceMaximum_eq, belowStartSup]
  apply le_antisymm
  · refine iSup_le fun k => iSup_le fun hk => iSup_le fun z => iSup_le fun hz => ?_
    rcases hz.1 with ⟨w, rfl⟩
    have hkt : k ≤ t := (le_of_lt hk).trans hjt
    have hw : w ∈ alignedIndex q k t :=
      (mem_alignedIndex_iff hq hkt).mpr hz.2
    refine le_iSup_of_le k (le_iSup_of_le hk
      (le_iSup_of_le w (le_iSup_of_le hw ?_)))
    change ENNReal.ofReal
        ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
          blockExcess (adaptedResponse q k w a) F) ≤ _
    exact le_rfl
  · refine iSup_le fun k => iSup_le fun hk => iSup_le fun w => iSup_le fun hw => ?_
    have hkt : k ≤ t := (le_of_lt hk).trans hjt
    let z : Vec d := adaptedCellCenter q k w
    have hz : z ∈ containedCenters q k t :=
      ⟨⟨w, rfl⟩, (mem_alignedIndex_iff hq hkt).mp hw⟩
    refine le_iSup_of_le k (le_iSup_of_le hk
      (le_iSup_of_le z (le_iSup_of_le hz ?_)))
    change ENNReal.ofReal
        ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
          blockExcess
            (coarseBlock
              (adaptedCellTranslate q k (adaptedCellCenter q k w)) a) F) ≤ _
    exact le_rfl

/-- The scalar size of one adapted response against a positive reference is an
almost-everywhere measurable statistic. -/
theorem aemeasurable_blockSize_adaptedResponse
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    AEMeasurable (fun a => blockSize (adaptedResponse q k w a) F) P := by
  have hU := Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w
  have hvol : 0 < (volume (adaptedCellAt q k w)).toReal := by
    exact ENNReal.toReal_pos (Recurrence.volume_adaptedCellAt_pos hq k w).ne'
      hU.volume_lt_top.ne
  exact (Window.measurable_blockSize_coarseBlock hU.isOpen
    hU.isBoundedDomain hvol hF hFpd).aemeasurable

/-- One weighted source-excess term is almost-everywhere measurable. -/
theorem aemeasurable_source_excess_term [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d} (hq : q.PosDef)
    (t k : ℤ) (w : Fin d → ℤ) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    AEMeasurable (fun a => ENNReal.ofReal
      ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
        blockExcess (adaptedResponse q k w a) F)) P := by
  have hsize := aemeasurable_blockSize_adaptedResponse (P := P) hq k w hF hFpd
  have hexc : AEMeasurable
      (fun a => blockExcess (adaptedResponse q k w a) F) P := by
    have hfun : (fun a => blockExcess (adaptedResponse q k w a) F) =
        fun a => max (blockSize (adaptedResponse q k w a) F - 1) 0 := by
      funext a
      have hA := Recurrence.isSymmetricBlockMat_adaptedResponse q k w a
      have hApsd := (posDef_toFullBlockMat hA
        (Recurrence.blockPosDef_adaptedResponse hq k w a)).posSemidef
      rw [blockExcess_eq hA hF hFpd hApsd,
        blockSize_eq_relSize hA hF hFpd hApsd]
    rw [hfun]
    exact (hsize.sub aemeasurable_const).max aemeasurable_const
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (hexc.const_mul ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ)))))

/-- The common below-start maximum is almost-everywhere measurable. -/
theorem aemeasurable_profileSourceMaximum [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (hjt : jStar ≤ t) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    AEMeasurable (profileSourceMaximum rhoMax q jStar t F) P := by
  have heq : profileSourceMaximum rhoMax q jStar t F = fun a =>
      ⨆ (k : ℤ) (_ : k < jStar) (w : Fin d → ℤ)
          (_ : w ∈ alignedIndex q k t),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))) *
            blockExcess (adaptedResponse q k w a) F) := by
    funext a
    exact profileSourceMaximum_eq_iSup_aligned hq hjt F a
  rw [heq]
  exact AEMeasurable.iSup fun k => AEMeasurable.iSup fun _ =>
    AEMeasurable.iSup fun w => AEMeasurable.iSup fun _ =>
      aemeasurable_source_excess_term hq t k w hF hFpd

/-- The complete terminal maximum is almost-everywhere measurable. -/
theorem aemeasurable_profileTotalMaximum [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (hjt : jStar ≤ t) {F : BlockMat d}
    (hEt : BlockPosDef (adaptedMean P q t))
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    AEMeasurable (profileTotalMaximum P rhoMax q jStar t F) P := by
  have hZ : AEMeasurable (profileCenteredMaximum P rhoMax q jStar t) P :=
    aemeasurable_profileCenteredMaximum (P := P) (q := q)
      (rhoMax := rhoMax) (jStar := jStar) (t := t) hq hEt
  have hB : AEMeasurable (profileSourceMaximum rhoMax q jStar t F) P :=
    aemeasurable_profileSourceMaximum (P := P) (rhoMax := rhoMax)
      (q := q) hq (jStar := jStar) (t := t) hjt hF hFpd
  exact hZ.add hB

/-- The `L^Q` seminorm of the complete maximum is the `Q`-th root of its
defining history. -/
theorem eLpNorm_profileTotalMaximum_eq
    {P : Measure (CoeffSpace d)} {Q rhoMax : ℝ} (hQ : 0 < Q)
    (q : Mat d) (jStar t : ℤ) (F : BlockMat d) :
    eLpNorm (profileTotalMaximum P rhoMax q jStar t F)
        (ENNReal.ofReal Q) P =
      profileTotalHistory P Q rhoMax q jStar t F ^ Q⁻¹ := by
  have hp0 : ENNReal.ofReal Q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hQ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hQ.le, one_div]
  simp only [enorm_eq_self]
  rfl

/-- Minkowski bounds the complete history by the centered history and the
source moment. -/
theorem profileTotalHistory_rpow_inv_le [NeZero d]
    {P : Measure (CoeffSpace d)} {Q rhoMax : ℝ} (hQ : 1 ≤ Q)
    {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} (hjt : jStar ≤ t)
    {F : BlockMat d} (hEt : BlockPosDef (adaptedMean P q t))
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    profileTotalHistory P Q rhoMax q jStar t F ^ Q⁻¹ ≤
      centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ +
        profileSourceMoment P Q rhoMax q jStar t F := by
  have hZ : AEStronglyMeasurable
      (profileCenteredMaximum P rhoMax q jStar t) P :=
    (aemeasurable_profileCenteredMaximum (P := P) (q := q)
      (rhoMax := rhoMax) (jStar := jStar) (t := t) hq hEt).aestronglyMeasurable
  have hB : AEStronglyMeasurable
      (profileSourceMaximum rhoMax q jStar t F) P :=
    (aemeasurable_profileSourceMaximum (P := P) (rhoMax := rhoMax)
      (q := q) hq (jStar := jStar) (t := t) hjt hF hFpd).aestronglyMeasurable
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Q := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_le_ofReal hQ
  have htri := eLpNorm_add_le hZ hB hp
  change eLpNorm (profileTotalMaximum P rhoMax q jStar t F)
      (ENNReal.ofReal Q) P ≤ _ at htri
  rw [eLpNorm_profileTotalMaximum_eq (by linarith only [hQ]),
    eLpNorm_profileCenteredMaximum_eq (by linarith only [hQ])] at htri
  change profileTotalHistory P Q rhoMax q jStar t F ^ Q⁻¹ ≤
      centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ +
        profileSourceMoment P Q rhoMax q jStar t F at htri
  exact htri

/-- The `L^Q` all-scale maximum is bounded by the complete history and terminal
drift. -/
theorem eLpNorm_diagonalWeakMaximum_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q rhoMax rhoDr rhoWn : ℝ} (hQ : 1 ≤ Q)
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn) {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (hjt : jStar ≤ t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1))) :
    eLpNorm (diagonalWeakMaximum rhoWn q t (adaptedMean P q t))
        (ENNReal.ofReal Q) P ≤
      profileTotalHistory P Q rhoMax q jStar t (adaptedMean P q t) ^ Q⁻¹ +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) := by
  let W := profileTotalMaximum P rhoMax q jStar t (adaptedMean P q t)
  let D : ℝ≥0∞ := ENNReal.ofReal (linearDrift P rhoDr q jStar t)
  have hpoint : ∀ a, diagonalWeakMaximum rhoWn q t (adaptedMean P q t) a ≤
      W a + D := fun a =>
    diagonalWeakMaximum_le_profileTotalMaximum_add_drift
      hrhoMax hrhoDr hrhoDrWn hq hEt hmono a
  have hmonoLp : eLpNorm (diagonalWeakMaximum rhoWn q t (adaptedMean P q t))
      (ENNReal.ofReal Q) P ≤ eLpNorm (fun a => W a + D) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_enorm fun a => ?_
    simpa only [enorm_eq_self] using hpoint a
  have hW : AEStronglyMeasurable W P :=
    (aemeasurable_profileTotalMaximum hq hjt hEt
      (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt).aestronglyMeasurable
  have hD : AEStronglyMeasurable (fun _ : CoeffSpace d => D) P :=
    aestronglyMeasurable_const
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Q := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_le_ofReal hQ
  have htri := eLpNorm_add_le hW hD hp
  have hconst : eLpNorm (fun _ : CoeffSpace d => D) (ENNReal.ofReal Q) P = D := by
    rw [eLpNorm_const _ (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith only [hQ]) (IsProbabilityMeasure.ne_zero P),
      measure_univ, ENNReal.one_rpow, mul_one, enorm_eq_self]
  exact hmonoLp.trans (htri.trans_eq (by
    rw [hconst, eLpNorm_profileTotalMaximum_eq (by linarith only [hQ])]))

/-- The full complete-maximum chain, including the centered/source split. -/
theorem eLpNorm_diagonalWeakMaximum_le_centered_source_drift [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q rhoMax rhoDr rhoWn : ℝ} (hQ : 1 ≤ Q)
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn) {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (hjt : jStar ≤ t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1))) :
    eLpNorm (diagonalWeakMaximum rhoWn q t (adaptedMean P q t))
        (ENNReal.ofReal Q) P ≤
      centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ +
        profileSourceMoment P Q rhoMax q jStar t (adaptedMean P q t) +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) := by
  exact (eLpNorm_diagonalWeakMaximum_le_profile hQ hrhoMax hrhoDr
    hrhoDrWn hq hjt hEt hmono).trans
      (add_le_add
        (profileTotalHistory_rpow_inv_le hQ hq hjt
          hEt (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt) le_rfl)

end

end Homogenization.HighContrast.Response
