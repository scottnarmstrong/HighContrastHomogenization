/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowMomentBound
import HCPoly.Provider.Transport.WhitneyRows
import HCPoly.Provider.Transport.DiscreteConvolution
import HCPoly.Provider.Transport.TransportCoefficients
import HCPoly.Setup.TransportObjects
import HCPoly.Provider.PortableHistory.CheckpointMoment
import HCPoly.Provider.ShortHop.SourceCoefficient
import HCPoly.Provider.Transport.TransportConclusion
import HCPoly.Provider.Transport.RowDischarge
import HCPoly.Provider.Transport.WindowWholeCell

/-!
# Terminal normalization for the two-grid bridge

The terminal adapted mean controls the reference block.  Combining this
comparison with the whole-cell estimate also controls every early target cell
by the ordered early coefficient used in the bridge source majorant.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- The mean of a coupled window multiplier is at most two. -/
theorem integral_windowMultiplier_le_two [IsProbabilityMeasure P]
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) :
    (∫ a, Y a ∂P) ≤ 2 := by
  have h := le_trans (Transport.ofReal_integral_le_lqNorm hY hQ)
    (Transport.lqNorm_le_two hQ hw hY)
  have h' : ENNReal.ofReal (∫ a, Y a ∂P) ≤ ENNReal.ofReal 2 := by
    simpa only [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num] using h
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h'

/-- A terminal adapted mean dominates the reference block with the terminal
boundary and multiplier factors displayed. -/
theorem reference_le_terminal_mean [NeZero d] [IsProbabilityMeasure P]
    (hCd : 0 < Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mr : Mat d} (hmr : mr.PosDef)
    (hqr : IsRoundedGrid jStar (roundedGrid jStar mr))
    {t : ℤ} (ht : jStar ≤ t)
    (hT : adaptedCell (roundedGrid jStar mr) t ⊆ centeredCube d M) :
    toFullBlockMat E ≤
      (kappaRef E * (boundaryConst Cd g mr * ∫ a, Y a ∂P)) •
        toFullBlockMat (adaptedMean P (roundedGrid jStar mr) t) := by
  let F : BlockMat d := adaptedMean P (roundedGrid jStar mr) t
  have hFsym : IsSymmetricBlockMat F :=
    Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mr) t
  have hFpd : Book.Ch02.BlockPosDef F :=
    Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hmr hqr ht hT
  have hsize : blockSize E F ≤
      kappaRef E * (boundaryConst Cd g mr * ∫ a, Y a ∂P) :=
    Transport.blockSize_adaptedMean_le hCd hg hE hEpd hY hmr hqr ht hT
  have hsand : toFullBlockMat E ≤ blockSize E F • toFullBlockMat F :=
    (PortableHistory.blockSize_sandwich hE hFsym hFpd).1
  have hFps : (toFullBlockMat F).PosSemidef :=
    (posDef_toFullBlockMat hFsym hFpd).posSemidef
  exact hsand.trans <| by
    change blockSize E F • toFullBlockMat F ≤
      (kappaRef E * (boundaryConst Cd g mr * ∫ a, Y a ∂P)) • toFullBlockMat F
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hFps.smul (sub_nonneg.mpr hsize)

/-- An early target mean is controlled by a later terminal mean with the
ordered early coefficient of the bridge. -/
theorem early_adaptedMean_le_terminal [NeZero d] [IsProbabilityMeasure P]
    (hCd : 1 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mv mr : Mat d} (hmv : mv.PosDef) (hmr : mr.PosDef)
    (hqv : IsRoundedGrid jStar (roundedGrid jStar mv))
    (hqr : IsRoundedGrid jStar (roundedGrid jStar mr))
    {j t : ℤ} (hj : jStar ≤ j) (ht : jStar ≤ t)
    (hW : adaptedCell (roundedGrid jStar mv) j ⊆ centeredCube d M)
    (hT : adaptedCell (roundedGrid jStar mr) t ⊆ centeredCube d M) :
    toFullBlockMat (adaptedMean P (roundedGrid jStar mv) j) ≤
      bridgeEarlyCoeff Cd g E mv mr •
        toFullBlockMat (adaptedMean P (roundedGrid jStar mr) t) := by
  let H : BlockMat d := adaptedMean P (roundedGrid jStar mv) j
  let F : BlockMat d := adaptedMean P (roundedGrid jStar mr) t
  have hCd0 : 0 < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hHsym : IsSymmetricBlockMat H :=
    Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mv) j
  have hFsym : IsSymmetricBlockMat F :=
    Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mr) t
  have hFpd : Book.Ch02.BlockPosDef F :=
    Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hmr hqr ht hT
  have hmean0 : 0 ≤ ∫ a, Y a ∂P :=
    le_trans zero_le_one (Transport.one_le_integral_of_isWindowMultiplier hY)
  have hmean2 : (∫ a, Y a ∂P) ≤ 2 :=
    integral_windowMultiplier_le_two hQ hw hY
  have hBv0 : 0 ≤ boundaryConst Cd g mv :=
    Transport.zero_le_boundaryConst hCd0.le hg mv
  have hBr0 : 0 ≤ boundaryConst Cd g mr :=
    Transport.zero_le_boundaryConst hCd0.le hg mr
  have hkap0 : 0 ≤ kappaRef E := Transport.zero_le_kappaRef E
  have hcell : adaptedCellTranslate (roundedGrid jStar mv) j
      (adaptedCellCenter (roundedGrid jStar mv) j 0) ⊆ centeredCube d M := by
    rw [← Transport.adaptedCellAt_eq_adaptedCellTranslate, PortableHistory.adaptedCellAt_zero]
    exact hW
  have hmeaneq : H = annealedBlock P
      (adaptedCellTranslate (roundedGrid jStar mv) j
        (adaptedCellCenter (roundedGrid jStar mv) j 0)) := by
    rw [show H = adaptedMean P (roundedGrid jStar mv) j by rfl,
      ← Transport.adaptedCellAt_eq_adaptedCellTranslate, PortableHistory.adaptedCellAt_zero]
    rfl
  have hfirst : blockSize H F ≤
      boundaryConst Cd g mv * (∫ a, Y a ∂P) * blockSize E F := by
    rw [hmeaneq]
    exact Transport.blockSize_annealedBlock_le hCd0.le hg hE hEpd hY hmv hqv
      hFsym hFpd hj _ hcell
  have hsecond : blockSize E F ≤
      kappaRef E * (boundaryConst Cd g mr * ∫ a, Y a ∂P) :=
    Transport.blockSize_adaptedMean_le hCd0 hg hE hEpd hY hmr hqr ht hT
  have hsq : (∫ a, Y a ∂P) * (∫ a, Y a ∂P) ≤ 4 := by
    nlinarith only [hmean0, hmean2]
  have hcommon : 0 ≤ kappaRef E * boundaryConst Cd g mv *
      boundaryConst Cd g mr := by positivity
  have hsize : blockSize H F ≤ bridgeEarlyCoeff Cd g E mv mr := by
    have hstep := mul_le_mul_of_nonneg_left hsecond (mul_nonneg hBv0 hmean0)
    have hmul := mul_le_mul_of_nonneg_left hsq hcommon
    have hCdstep := mul_le_mul_of_nonneg_right hCd
      (mul_nonneg hcommon (by norm_num : (0 : ℝ) ≤ 4))
    rw [bridgeEarlyCoeff]
    nlinarith only [hfirst, hstep, hmul, hCdstep]
  have hsand : toFullBlockMat H ≤ blockSize H F • toFullBlockMat F :=
    (PortableHistory.blockSize_sandwich hHsym hFsym hFpd).1
  have hFps : (toFullBlockMat F).PosSemidef :=
    (posDef_toFullBlockMat hFsym hFpd).posSemidef
  exact hsand.trans <| by
    change blockSize H F • toFullBlockMat F ≤
      bridgeEarlyCoeff Cd g E mv mr • toFullBlockMat F
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hFps.smul (sub_nonneg.mpr hsize)

/-- The below-alignment expectation row, in its reference-block form, is
normalized by a terminal adapted mean and absorbed by the continued bridge
coefficient. -/
theorem below_start_mean_le_terminal [NeZero d] [IsProbabilityMeasure P]
    (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv mr : Mat d} (hmr : mr.PosDef)
    (hqr : IsRoundedGrid jStar (roundedGrid jStar mr))
    {j t : ℤ} (hj : jStar ≤ j) (ht : jStar ≤ t)
    (hT : adaptedCell (roundedGrid jStar mr) t ⊆ centeredCube d M) :
    (6 * (d : ℝ) * Real.sqrt d *
        gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
        boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - j) *
          (∫ a, Y a ∂P)) • toFullBlockMat E ≤
      (18 * (d : ℝ) * Real.sqrt d *
        bridgeContCoeff Cd g E jStar mp mv mr *
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ)))) •
        toFullBlockMat (adaptedMean P (roundedGrid jStar mr) t) := by
  let F : BlockMat d := adaptedMean P (roundedGrid jStar mr) t
  have hCd0 : 0 < Cd := lt_of_lt_of_le zero_lt_one hCd
  have href := reference_le_terminal_mean hCd0 hg hE hEpd hY hmr hqr ht hT
  have hmean0 : 0 ≤ ∫ a, Y a ∂P :=
    le_trans zero_le_one (Transport.one_le_integral_of_isWindowMultiplier hY)
  have hmean2 : (∫ a, Y a ∂P) ≤ 2 :=
    integral_windowMultiplier_le_two hQ hw hY
  have hmeansq : (∫ a, Y a ∂P) * (∫ a, Y a ∂P) ≤ 4 := by
    nlinarith only [hmean0, hmean2]
  have hgrid : 0 ≤ gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) :=
    le_trans zero_le_one (Transport.one_le_gridRatio _ _)
  have hBmp : 0 ≤ boundaryConst Cd g mp :=
    Transport.zero_le_boundaryConst hCd0.le hg mp
  have hBmr : 0 ≤ boundaryConst Cd g mr :=
    Transport.zero_le_boundaryConst hCd0.le hg mr
  have hkap : 0 ≤ kappaRef E := Transport.zero_le_kappaRef E
  have hchi : 0 ≤ chiG g := (Transport.zero_lt_chiG hg).le
  have hzeta0 : 0 ≤ zetaG g := (Transport.zero_lt_zetaG hg).le
  have hzeta : zetaG g ≤ 3 * chiG g := Transport.zetaG_le_three_mul_chiG hg0 hg
  have hrate : (3 : ℝ) ^ (jStar - j) ≤
      (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) :=
    Transport.zpow_le_rpow_boundary_rate hg0 hj
  have hraw0 : 0 ≤ 6 * (d : ℝ) * Real.sqrt d *
      gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
      boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - j) *
        (∫ a, Y a ∂P) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by positivity) hgrid) hBmp) hzeta0) (zpow_nonneg (by norm_num) _)) hmean0
  have hscaled := smul_le_smul_of_le hraw0 href
  have hcommon : 0 ≤ 6 * (d : ℝ) * Real.sqrt d *
      gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
      boundaryConst Cd g mp * kappaRef E * boundaryConst Cd g mr := by
    positivity
  have hcoef :
      (6 * (d : ℝ) * Real.sqrt d *
          gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
          boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - j) *
            (∫ a, Y a ∂P)) *
          (kappaRef E * (boundaryConst Cd g mr * ∫ a, Y a ∂P)) ≤
        18 * (d : ℝ) * Real.sqrt d *
          bridgeContCoeff Cd g E jStar mp mv mr *
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) := by
    have hzpow0 : 0 ≤ (3 : ℝ) ^ (jStar - j) := zpow_nonneg (by norm_num) _
    have hrate0 : 0 ≤ (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have h3chi0 : 0 ≤ 3 * chiG g := mul_nonneg (by norm_num) hchi
    have hzr := mul_le_mul hzeta hrate hzpow0 h3chi0
    have hzrm := mul_le_mul hzr hmeansq
      (mul_nonneg hmean0 hmean0) (mul_nonneg h3chi0 hrate0)
    have hinner :
        (zetaG g * (3 : ℝ) ^ (jStar - j)) *
            ((∫ a, Y a ∂P) * ∫ a, Y a ∂P) ≤
          Cd * ((3 * chiG g *
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ)))) * 4) := by
      refine hzrm.trans ?_
      have hright0 : 0 ≤ (3 * chiG g *
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ)))) * 4 := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hCd hright0
    have hfinal := mul_le_mul_of_nonneg_left hinner hcommon
    rw [bridgeContCoeff]
    convert hfinal using 1 <;> ring
  have hFsym : IsSymmetricBlockMat F :=
    Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mr) t
  have hFpd : Book.Ch02.BlockPosDef F :=
    Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hmr hqr ht hT
  have hFps : (toFullBlockMat F).PosSemidef :=
    (posDef_toFullBlockMat hFsym hFpd).posSemidef
  exact hscaled.trans <| by
    change
      (6 * (d : ℝ) * Real.sqrt d *
          gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
          boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - j) *
            (∫ a, Y a ∂P)) •
        ((kappaRef E * (boundaryConst Cd g mr * ∫ a, Y a ∂P)) •
          toFullBlockMat F) ≤
      (18 * (d : ℝ) * Real.sqrt d *
        bridgeContCoeff Cd g E jStar mp mv mr *
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ)))) • toFullBlockMat F
    rw [smul_smul]
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hFps.smul (sub_nonneg.mpr hcoef)

end

end Bridge
end HighContrast
end Homogenization
