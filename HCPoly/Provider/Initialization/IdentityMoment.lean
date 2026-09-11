/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.IdentityMean
import HCPoly.Provider.Initialization.Moments

/-!
# Centered moment on the identity grid

The standard-cell window row has coefficient one.  Combined with the sharp
reference comparison, it yields the identity constant without a boundary
eccentricity factor.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The centered identity-grid response has the source initialization moment
bound with the explicit dimensional factor used by the general grid proof. -/
theorem identity_centeredMoment_le [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M r : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hjr : jStar ≤ r) (hrM : r ≤ M) :
    centeredMoment P ((initExpQ d g : ℕ) : ℝ)
        (roundedGrid jStar (1 : Mat d)) r ≤
      ENNReal.ofReal
        ((2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
            (1 + 2 * (d : ℝ))) * initIdentityConst E) := by
  set q : Mat d := roundedGrid jStar (1 : Mat d) with hq
  set Em : BlockMat d := adaptedMean P q r with hEm
  set Q : ℝ := ((initExpQ d g : ℕ) : ℝ) with hQdef
  set C : ℝ := initIdentityConst E with hCdef
  set L : ℝ := (2 * d : ℝ) ^ Q⁻¹ * (1 + 2 * (d : ℝ)) with hLdef
  have hQ2 : (2 : ℝ) ≤ Q := by
    rw [hQdef]
    exact two_le_initExpQ hg
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num) hQ2
  have hindex := identity_admissible_index hw hjr hrM
  have hqgrid := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow
    hw Matrix.PosDef.one
  rw [← hq] at hqgrid
  have hmean := identity_mean_reference_comparison hg hE hEpd hw hY hjr hrM
  rw [← hq, ← hEm] at hmean
  have hEmSymm : IsSymmetricBlockMat Em := by
    rw [hEm]
    exact Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hEmPd : Book.Ch02.BlockPosDef Em := by
    rw [hEm]
    exact (finite_and_posDef_of_admissible hw hY Matrix.PosDef.one hindex).2
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    exact one_le_initIdentityConst hE hEpd hsharp
  have hcell : standardCell d r 0 ⊆ centeredCube d M := by
    rw [standardCell_zero]
    exact centeredCube_subset_centeredCube hrM
  have hpath : ∀ᵐ a ∂P,
      BlockMatLoewnerLE (coarseBlock (adaptedCell q r) a)
        (blockScale (Y a) E) := by
    filter_upwards [hY.standard_primal] with a ha
    have h := ha r 0 hcell
    rw [burnDiscount_eq_one hjr, mul_one] at h
    simpa only [standardCell_zero, hq, roundedGrid_one hw, adaptedCell_one] using h
  have hpt : ∀ᵐ a ∂P,
      schattenSize Q (blockSub (coarseBlock (adaptedCell q r) a) Em) Em ≤
        L * C * Y a := by
    filter_upwards [hpath] with a ha
    have hAsymm : IsSymmetricBlockMat (coarseBlock (adaptedCell q r) a) :=
      isSymmetricBlockMat_coarseBlock _ a
    have hApsd : (toFullBlockMat (coarseBlock (adaptedCell q r) a)).PosSemidef :=
      (posDef_toFullBlockMat hAsymm
        (Recurrence.blockPosDef_coarseBlock_adaptedCell
          (Recurrence.posDef_of_isRoundedGrid hqgrid) r a)).posSemidef
    have hdom0 := toFullBlockMat_response_le_reference_mul
      hAsymm hE hEpd hsharp hEmSymm hEmPd
      (show (1 : ℝ) ≤ 1 by norm_num) (hY.one_le a)
      (by simpa only [one_mul] using ha)
      (by simpa only [one_mul] using hmean.1)
    have hdom : toFullBlockMat (coarseBlock (adaptedCell q r) a) ≤
        (C * Y a) • toFullBlockMat Em := by
      rw [hCdef, initIdentityConst]
      convert hdom0 using 1
      ring_nf
    have hcY : 1 ≤ C * Y a :=
      one_le_mul_of_one_le_of_one_le hC1 (hY.one_le a)
    have hsize := raw_and_centered_schattenSize_le hAsymm hApsd hEmSymm
      hEmPd hQ0 hcY hdom
    rw [hLdef]
    simpa only [mul_assoc] using hsize.2
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hLC0 : 0 ≤ L * C := mul_nonneg hL0 hC0
  have hcenter : centeredMoment P Q q r ≤
      eLpNorm ((L * C) • Y) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hpt] with a ha
    have hleft : 0 ≤ schattenSize Q
        (blockSub (coarseBlock (adaptedCell q r) a) Em) Em :=
      Recurrence.zero_le_schattenNorm
        (isSymmetricBlockMat_normalizedBlock
          (isSymmetricBlockMat_blockSub
            (isSymmetricBlockMat_coarseBlock _ a) hEmSymm)) Q
    change ‖schattenSize Q
      (blockSub (coarseBlock (adaptedCell q r) a) Em) Em‖ ≤ ‖(L * C) * Y a‖
    rw [Real.norm_of_nonneg hleft,
      Real.norm_of_nonneg
        (mul_nonneg hLC0 (le_trans zero_le_one (hY.one_le a)))]
    exact ha
  have hYnorm : lqNorm P Q Y ≤ 2 := by
    rw [hQdef]
    exact (initialization_multiplier_bounds hg hw hY).2
  have hcommon : eLpNorm ((L * C) • Y) (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal ((2 * L) * C) := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hLC0]
    calc
      ENNReal.ofReal (L * C) * lqNorm P Q Y ≤ ENNReal.ofReal (L * C) * 2 :=
        by gcongr
      _ = ENNReal.ofReal ((2 * L) * C) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_mul hLC0]
        congr 1
        ring
  have hresult := hcenter.trans hcommon
  simpa only [hQdef, hq, hEm, hLdef, hCdef, mul_assoc] using hresult

end

end Initialization
end HighContrast
end Homogenization
