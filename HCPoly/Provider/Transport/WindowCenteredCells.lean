/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowCenteredBound

/-!
# The centered supremum of a retained family, pathwise

In the whole-cell regime of `e.source.adapted.bound` the centered supremum
`\sup_{W\in\mathcal W}|F^{-1/2}(\bfA(W)-\E[\bfA(W)])F^{-1/2}|_{S_Q}` is bounded
along every realization by the centered cell bound applied to each member: the
response of a member is below `B_{\mathbf q'}Y_P𝐄` and its mean is below
`B_{\mathbf q'}\E[Y_P]𝐄`, so that bound gives
`(2d)^{1/Q}B_{\mathbf q'}Λ(F;𝐄)(Y_P+\E[Y_P])` uniformly in the member.

The bound does not depend on the member, so the supremum inherits it whatever
the family — this is the sense in which the printed clause carries no
cardinality factor.  The adjoint supremum is the same argument with the
reflected data: the sharp adjoint response is the reflection of the response,
the sharp adjoint mean is the reflection of the mean, and the reflected
normalization is the same real number `Λ(F;𝐄)`.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

section Family

variable (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
  (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
  (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {F : BlockMat d}
  (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {Q : ℝ} (hQ : 0 < Q)
  {j : ℤ} (hj : jStar ≤ j) {W : Set (Set (Vec d))}
  (hWmem : ∀ V ∈ W, ∃ y : Vec d, V = adaptedCellTranslate (roundedGrid jStar nu) j y)
  (hWcont : ∀ V ∈ W, V ⊆ centeredCube d M)

include hCd hg hE hY hnu hq hF hFpd hQ hj hWmem hWcont in
/-- **The centered supremum of the whole-cell regime, pathwise.**  One event of
full measure carries the bound for every member of the family. -/
theorem ae_cellFamilyCenteredSup_le [IsProbabilityMeasure P] :
    ∀ᵐ a ∂P, cellFamilyCenteredSup P Q W F a ≤
      ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F *
        (Y a + ∫ b, Y b ∂P)) := by
  have hB := zero_le_boundaryConst hCd hg nu
  have hmean : (0 : ℝ) ≤ ∫ b, Y b ∂P :=
    le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  filter_upwards [hY.adapted_primal] with a ha
  have hY1 : (0 : ℝ) ≤ Y a := le_trans zero_le_one (hY.one_le a)
  simp only [cellFamilyCenteredSup]
  refine iSup_le fun V => iSup_le fun hV => ?_
  obtain ⟨y, rfl⟩ := hWmem V hV
  refine ENNReal.ofReal_le_ofReal ?_
  have hcont := hWcont _ hV
  have hint := hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu hq j y hcont
  have hpos := fun b => blockPosDef_coarseBlock_adaptedCellTranslate
    (Recurrence.posDef_of_isRoundedGrid hq) j y b
  have hAsym := isSymmetricBlockMat_coarseBlock
    (adaptedCellTranslate (roundedGrid jStar nu) j y) a
  have hAmsym := Recurrence.isSymmetricBlockMat_annealedBlock P
    (adaptedCellTranslate (roundedGrid jStar nu) j y)
  have hAle : BlockMatLoewnerLE
      (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) j y) a)
      (blockScale (boundaryConst Cd g nu * Y a) E) := by
    have h := ha nu hnu j y hcont
    rwa [burnDiscount_eq_one g hj, mul_one] at h
  refine (schattenSize_blockSub_le_of_bounds hQ hAsym
    (posDef_toFullBlockMat hAsym (hpos a)).posSemidef hAmsym
    (posDef_toFullBlockMat hAmsym (blockPosDef_annealedBlock hint hpos)).posSemidef
    hE hF hFpd (mul_nonneg hB hY1) (mul_nonneg hB hmean) hAle
    (annealedBlock_le_blockScale hE hY hnu hq hj y hcont)).trans (le_of_eq (by ring))

include hCd hg hE hY hnu hq hF hFpd hQ hj hWmem hWcont in
/-- **The adjoint centered supremum of the whole-cell regime, pathwise**: the
same bound with the reflected data. -/
theorem ae_cellFamilyCenteredSupAdjoint_le [IsProbabilityMeasure P] :
    ∀ᵐ a ∂P, cellFamilyCenteredSupAdjoint P Q W (blockReflect F) a ≤
      ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F *
        (Y a + ∫ b, Y b ∂P)) := by
  have hB := zero_le_boundaryConst hCd hg nu
  have hmean : (0 : ℝ) ≤ ∫ b, Y b ∂P :=
    le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  filter_upwards [hY.adapted_adjoint] with a ha
  have hY1 : (0 : ℝ) ≤ Y a := le_trans zero_le_one (hY.one_le a)
  simp only [cellFamilyCenteredSupAdjoint, annealedStarInv]
  refine iSup_le fun V => iSup_le fun hV => ?_
  obtain ⟨y, rfl⟩ := hWmem V hV
  refine ENNReal.ofReal_le_ofReal ?_
  have hcont := hWcont _ hV
  have hint := hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu hq j y hcont
  have hpos := fun b => blockPosDef_coarseBlock_adaptedCellTranslate
    (Recurrence.posDef_of_isRoundedGrid hq) j y b
  have hAsym := isSymmetricBlockMat_coarseStarInv
    (adaptedCellTranslate (roundedGrid jStar nu) j y) a
  have hAmsym := isSymmetricBlockMat_blockReflect (Recurrence.isSymmetricBlockMat_annealedBlock P
    (adaptedCellTranslate (roundedGrid jStar nu) j y))
  have hAle : BlockMatLoewnerLE
      (coarseStarInv (adaptedCellTranslate (roundedGrid jStar nu) j y) a)
      (blockScale (boundaryConst Cd g nu * Y a) (blockReflect E)) := by
    have h := ha nu hnu j y hcont
    rwa [burnDiscount_eq_one g hj, mul_one] at h
  have hAmle : BlockMatLoewnerLE
      (blockReflect (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) j y)))
      (blockScale (boundaryConst Cd g nu * ∫ b, Y b ∂P) (blockReflect E)) := by
    rw [blockScale_blockReflect]
    exact blockMatLoewnerLE_blockReflect
      (annealedBlock_le_blockScale hE hY hnu hq hj y hcont)
  have hstep := schattenSize_blockSub_le_of_bounds hQ hAsym
    (posDef_toFullBlockMat hAsym (blockPosDef_blockReflect (hpos a))).posSemidef hAmsym
    (posDef_toFullBlockMat hAmsym
      (blockPosDef_blockReflect (blockPosDef_annealedBlock hint hpos))).posSemidef
    (isSymmetricBlockMat_blockReflect hE) (isSymmetricBlockMat_blockReflect hF)
    (blockPosDef_blockReflect hFpd) (mul_nonneg hB hY1) (mul_nonneg hB hmean) hAle hAmle
  rw [blockSize_blockReflect] at hstep
  exact hstep.trans (le_of_eq (by ring))

end Family

end

end Transport
end HighContrast
end Homogenization
