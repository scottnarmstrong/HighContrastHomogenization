/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowTerminalNormalization

/-!
# The whole-cell regime: the cell bound and the mean suprema

When the target scale is below the buffer, `j < j_* + \ell_0`, the filling of
`e.source.adapted.bound` is not used at all: every member of the cell family
is retained whole, and the estimates it needs are the cell bound of the window
applied directly to each member.  This file proves the whole-cell source bound
at the early target scales in both orientations, the integrability of the
response over each member, and the two mean suprema of the early target cells.

The cells of the family are translates of the adapted cell of the new grid at a
scale at or above the alignment, so the burn discount is one and the same
multiplier serves them all on one event of full measure — there is no
multiplicity in the family.  The mean supremum is then the cell bound
integrated, followed by one change of reference block, which costs exactly
`Λ(F;𝐄)`.

The adjoint mean supremum needs no separate argument.  The sharp adjoint
annealed block is the reflection of the annealed block, the dual reference block
is the reflection of the reference block, and the scalar size is invariant under
the reflection, so the two suprema are the same extended real.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-! ## The pathwise cell bound -/

/-- **The whole-cell source bound at the early target scales**: on one
event of full measure the response of every retained cell is below
`B_{\mathbf q'}Y_P𝐄` and its sharp adjoint is below the same multiple of the
dual reference block. -/
theorem ae_whole_cell_packet (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {nu : Mat d} (hnu : nu.PosDef) {j : ℤ} (hj : jStar ≤ j)
    {W : Set (Set (Vec d))}
    (hWmem : ∀ V ∈ W, ∃ y : Vec d, V = adaptedCellTranslate (roundedGrid jStar nu) j y)
    (hWcont : ∀ V ∈ W, V ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, ∀ V ∈ W,
      BlockMatLoewnerLE (coarseBlock V a)
          (blockScale (boundaryConst Cd g nu * Y a) E) ∧
        BlockMatLoewnerLE (coarseStarInv V a)
          (blockScale (boundaryConst Cd g nu * Y a) (blockReflect E)) := by
  filter_upwards [hY.adapted_primal, hY.adapted_adjoint] with a hp hadj
  intro V hV
  obtain ⟨y, rfl⟩ := hWmem V hV
  refine ⟨?_, ?_⟩
  · have h := hp nu hnu j y (hWcont _ hV)
    rwa [burnDiscount_eq_one g hj, mul_one] at h
  · have h := hadj nu hnu j y (hWcont _ hV)
    rwa [burnDiscount_eq_one g hj, mul_one] at h

/-- **The response of every retained cell is integrable over the law**, so the
mean suprema of the whole-cell regime denote. -/
theorem hasIntegrableCoarseBlock_of_mem
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {j : ℤ} {W : Set (Set (Vec d))}
    (hWmem : ∀ V ∈ W, ∃ y : Vec d, V = adaptedCellTranslate (roundedGrid jStar nu) j y)
    (hWcont : ∀ V ∈ W, V ⊆ centeredCube d M) :
    ∀ V ∈ W, HasIntegrableCoarseBlock P V := by
  intro V hV
  obtain ⟨y, rfl⟩ := hWmem V hV
  exact hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu hq j y (hWcont _ hV)

/-! ## The mean of one retained cell -/

/-- **The normalized mean of one retained cell.**  The cell bound integrates to a
Loewner bound by `B_{\mathbf q'}\E[Y_P]𝐄`, and a change of reference block from
`𝐄` to `F` costs `Λ(F;𝐄)`. -/
theorem blockSize_annealedBlock_le [IsProbabilityMeasure P] (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {j : ℤ}
    (hj : jStar ≤ j) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) j y ⊆ centeredCube d M) :
    blockSize (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) j y)) F ≤
      boundaryConst Cd g nu * (∫ a, Y a ∂P) * blockSize E F := by
  have hint := hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu hq j y hcont
  have hAsym := Recurrence.isSymmetricBlockMat_annealedBlock P
    (adaptedCellTranslate (roundedGrid jStar nu) j y)
  have hApd : Book.Ch02.BlockPosDef
      (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) j y)) :=
    blockPosDef_annealedBlock hint fun a =>
      blockPosDef_coarseBlock_adaptedCellTranslate (Recurrence.posDef_of_isRoundedGrid hq) j y a
  have hAps := (posDef_toFullBlockMat hAsym hApd).posSemidef
  have hlam : 0 ≤ blockSize E F := PortableHistory.blockSize_nonneg hE hF hFpd
  have hmean : (0 : ℝ) ≤ ∫ a, Y a ∂P :=
    le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  have h1 : blockSize (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) j y)) E ≤
      boundaryConst Cd g nu * ∫ a, Y a ∂P :=
    blockSize_le_of_blockMatLoewnerLE_blockScale hAsym hAps hE hEpd
      (mul_nonneg (zero_le_boundaryConst hCd hg nu) hmean)
      (annealedBlock_le_blockScale hE hY hnu hq hj y hcont)
  have h2 := PortableHistory.blockSize_le_mul_blockSize hAsym hE hEpd hF hFpd hlam
    (PortableHistory.blockSize_sandwich hE hF hFpd).1
  calc blockSize (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) j y)) F
      ≤ blockSize E F *
          blockSize (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) j y)) E :=
        h2
    _ ≤ blockSize E F * (boundaryConst Cd g nu * ∫ a, Y a ∂P) :=
        mul_le_mul_of_nonneg_left h1 hlam
    _ = boundaryConst Cd g nu * (∫ a, Y a ∂P) * blockSize E F := by ring

/-! ## The two mean suprema -/

section Family

variable (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
  (hEpd : Book.Ch02.BlockPosDef E)
  (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
  (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {F : BlockMat d}
  (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {j : ℤ}
  (hj : jStar ≤ j) {W : Set (Set (Vec d))}
  (hWmem : ∀ V ∈ W, ∃ y : Vec d, V = adaptedCellTranslate (roundedGrid jStar nu) j y)
  (hWcont : ∀ V ∈ W, V ⊆ centeredCube d M)

include hCd hg hE hEpd hY hnu hq hF hFpd hj hWmem hWcont in
/-- **The mean supremum of the whole-cell regime**, the mean of the early target
cells. -/
theorem cellFamilyMeanSup_le [IsProbabilityMeasure P] :
    cellFamilyMeanSup P W F ≤
      ENNReal.ofReal (boundaryConst Cd g nu * (∫ a, Y a ∂P) * blockSize E F) := by
  simp only [cellFamilyMeanSup]
  refine iSup_le fun V => iSup_le fun hV => ?_
  obtain ⟨y, rfl⟩ := hWmem V hV
  exact ENNReal.ofReal_le_ofReal
    (blockSize_annealedBlock_le hCd hg hE hEpd hY hnu hq hF hFpd hj y (hWcont _ hV))

include hCd hg hE hEpd hY hnu hq hF hFpd hj hWmem hWcont in
/-- **The adjoint mean supremum of the whole-cell regime**: the same bound, the
two scalar normalizations agreeing by the reflection identity. -/
theorem cellFamilyMeanSupAdjoint_le [IsProbabilityMeasure P] :
    cellFamilyMeanSupAdjoint P W (blockReflect F) ≤
      ENNReal.ofReal (boundaryConst Cd g nu * (∫ a, Y a ∂P) * blockSize E F) := by
  simp only [cellFamilyMeanSupAdjoint, annealedStarInv, blockSize_blockReflect]
  refine iSup_le fun V => iSup_le fun hV => ?_
  obtain ⟨y, rfl⟩ := hWmem V hV
  exact ENNReal.ofReal_le_ofReal
    (blockSize_annealedBlock_le hCd hg hE hEpd hY hnu hq hF hFpd hj y (hWcont _ hV))

end Family

end

end Transport
end HighContrast
end Homogenization
