/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileDefectIdentities
import HCPoly.Provider.Response.ProfileRecentCellSum
import HCPoly.Provider.Response.DiagonalWeakNormAdjointCarriers

/-!
# Bounds for the positive response defects

The terminal geometry normalizes a mean increment by the terminal annealed
block.  Its scalar size is controlled by the root of `frakH`, and the scale-`s`
summand of the nonlinear history supplies the exact window weight.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- A recentered positive block remains symmetric and positive definite. -/
theorem profileRecenteredMean_symm_posDef
    {P : Measure (CoeffSpace d)} {q g : Mat d} {t : ℤ}
    (hEt : BlockPosDef (adaptedMean P q t)) :
    IsSymmetricBlockMat (profileRecenteredMean P q g t) ∧
      BlockPosDef (profileRecenteredMean P q g t) := by
  have hbase : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt
  have hfull : (toFullBlockMat (profileRecenteredMean P q g t)).PosDef := by
    simp only [profileRecenteredMean, toFullBlockMat_blockMatMul,
      toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG]
    simpa only [Matrix.mul_assoc] using
      posDef_conj hbase (isUnit_fullBlockShear g)
  have hsymm : IsSymmetricBlockMat (profileRecenteredMean P q g t) :=
    isSymmetricBlockMat_of_posSemidef hfull.posSemidef
  exact ⟨hsymm, (blockPosDef_iff_posDef hsymm).mpr hfull⟩

/-- The quadratic form of a recentered mean increment is the original
increment read at the sheared load. -/
theorem profileRecenteredMean_increment_quadratic
    (P : Measure (CoeffSpace d)) (q g : Mat d) (s t : ℤ)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (blockSub (profileRecenteredMean P q g s)
            (profileRecenteredMean P q g t)) X) =
      blockVecDot (blockMatVecMul (blockG g) X)
        (blockMatVecMul
          (blockSub (adaptedMean P q s) (adaptedMean P q t))
          (blockMatVecMul (blockG g) X)) := by
  rw [blockMatVecMul_blockSub, blockVecDot_sub_right,
    blockMatVecMul_blockSub, blockVecDot_sub_right,
    profileRecenteredMean_quadratic, profileRecenteredMean_quadratic]

/-- The quadratic form of a recentered adjoint mean increment is the original
increment read at the signed, sheared load. -/
theorem profileRecenteredAdjointMean_increment_quadratic
    (P : Measure (CoeffSpace d)) (q g : Mat d) (s t : ℤ)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (blockSub (profileRecenteredAdjointMean P q g s)
            (profileRecenteredAdjointMean P q g t)) X) =
      blockVecDot
        (blockMatVecMul (blockG g)
          (blockMatVecMul (blockDiag 1 (-1)) X))
        (blockMatVecMul
          (blockSub (adaptedMean P q s) (adaptedMean P q t))
          (blockMatVecMul (blockG g)
            (blockMatVecMul (blockDiag 1 (-1)) X))) := by
  rw [blockMatVecMul_blockSub, blockVecDot_sub_right,
    blockMatVecMul_blockSub, blockVecDot_sub_right,
    profileRecenteredAdjointMean_quadratic,
    profileRecenteredAdjointMean_quadratic]

/-- A positive mean increment is bounded at every load by its terminal
quadratic form times the root of the nonlinear gain. -/
theorem adaptedMean_increment_quadratic_le_frakH [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} {s t : ℤ} {Q : ℝ}
    (hQ : 1 ≤ Q) (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s)) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (blockSub (adaptedMean P q s) (adaptedMean P q t)) X) ≤
      blockVecDot X (blockMatVecMul (adaptedMean P q t) X) *
        frakH Q (relMean P q s t) ^ Q⁻¹ := by
  let H := blockSub (adaptedMean P q s) (adaptedMean P q t)
  let Et := adaptedMean P q t
  have hHsymm : IsSymmetricBlockMat H :=
    isSymmetricBlockMat_blockSub
      (Recurrence.isSymmetricBlockMat_adaptedMean P q s)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
  have hEtsymm : IsSymmetricBlockMat Et :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hsandwich := (PortableHistory.blockSize_sandwich hHsymm hEtsymm hEt).1
  have hraw := Initialization.dotProduct_mulVec_le_of_le hsandwich (toFullBlockVec X)
  have hquad : blockVecDot X (blockMatVecMul H X) ≤
      blockSize H Et * blockVecDot X (blockMatVecMul Et X) := by
    simpa only [blockVecDot_blockMatVecMul_eq_dotProduct,
      Matrix.smul_mulVec, dotProduct_smul, star_trivial, smul_eq_mul] using hraw
  have hterminal : 0 ≤ blockVecDot X (blockMatVecMul Et X) := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    exact (posDef_toFullBlockMat hEtsymm hEt).posSemidef.dotProduct_mulVec_nonneg _
  have hsize := blockSize_adaptedMean_sub_le_frakH hQ hEt hmean
  dsimp only [H, Et] at hquad hterminal ⊢
  calc
    blockVecDot X
        (blockMatVecMul
          (blockSub (adaptedMean P q s) (adaptedMean P q t)) X) ≤
        blockSize (blockSub (adaptedMean P q s) (adaptedMean P q t))
            (adaptedMean P q t) *
          blockVecDot X (blockMatVecMul (adaptedMean P q t) X) := hquad
    _ ≤ (frakH Q (relMean P q s t) ^ Q⁻¹) *
          blockVecDot X (blockMatVecMul (adaptedMean P q t) X) :=
      mul_le_mul_of_nonneg_right hsize hterminal
    _ = blockVecDot X (blockMatVecMul (adaptedMean P q t) X) *
          frakH Q (relMean P q s t) ^ Q⁻¹ := mul_comm _ _

/-- The primal response defect is controlled by its own terminal load and the
root of the relative-mean gain. -/
theorem profilePrimalResponseDefect_le_frakH [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} {Q : ℝ} (hQ : 1 ≤ Q)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s)) (pMinus qMinus : Vec d) :
    profilePrimalResponseDefect P hq g hg s t pMinus qMinus ≤
      (1 / 2 : ℝ) *
        diagonalWeakLoadMinus (profileRecenteredMean P q g t)
            pMinus qMinus ^ 2 *
          frakH Q (relMean P q s t) ^ Q⁻¹ := by
  let X : BlockVec d := (-pMinus, qMinus)
  have hbase := adaptedMean_increment_quadratic_le_frakH hQ hEt hmean
    (blockMatVecMul (blockG g) X)
  rw [← profileRecenteredMean_increment_quadratic P q g s t X,
    ← profileRecenteredMean_quadratic P q g t X] at hbase
  obtain ⟨hEhat, hEhatpd⟩ := profileRecenteredMean_symm_posDef (g := g) hEt
  have hload := sq_diagonalWeakLoadMinus
    (p := pMinus) (q := qMinus) hEhat hEhatpd
  rw [hload]
  rw [profilePrimalResponseDefect_identity hq hg hints hintt]
  change (1 / 2 : ℝ) * blockVecDot X
      (blockMatVecMul
        (blockSub (profileRecenteredMean P q g s)
          (profileRecenteredMean P q g t)) X) ≤ _
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [mul_assoc] using hscaled

/-- The adjoint response defect is controlled by its independent positive load
and the same relative-mean gain. -/
theorem profileAdjointResponseDefect_le_frakH [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} {Q : ℝ} (hQ : 1 ≤ Q)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s)) (pPlus qPlus : Vec d) :
    profileAdjointResponseDefect P hq g hg s t pPlus qPlus ≤
      (1 / 2 : ℝ) *
        diagonalWeakLoadPlus (profileRecenteredMean P q g t)
            pPlus qPlus ^ 2 *
          frakH Q (relMean P q s t) ^ Q⁻¹ := by
  let X : BlockVec d := (-pPlus, qPlus)
  let DX := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  have hbase := adaptedMean_increment_quadratic_le_frakH hQ hEt hmean
    (blockMatVecMul (blockG g) DX)
  rw [← profileRecenteredAdjointMean_increment_quadratic P q g s t X,
    ← profileRecenteredAdjointMean_quadratic P q g t X] at hbase
  obtain ⟨hEhat, hEhatpd⟩ := profileRecenteredMean_symm_posDef (g := g) hEt
  have hEad := isSymmetricBlockMat_adjointSign_congr hEhat
  have hEadpd := blockPosDef_adjointSign_congr hEhatpd
  have hload :
      diagonalWeakLoadPlus (profileRecenteredMean P q g t)
          pPlus qPlus ^ 2 =
        blockVecDot ((-pPlus, qPlus) : BlockVec d)
          (blockMatVecMul (profileRecenteredAdjointMean P q g t)
            ((-pPlus, qPlus) : BlockVec d)) := by
    calc
      diagonalWeakLoadPlus (profileRecenteredMean P q g t)
            pPlus qPlus ^ 2 =
          diagonalWeakLoadMinus
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (profileRecenteredMean P q g t)
                (blockDiag 1 (-1)))) pPlus qPlus ^ 2 := by
        rw [diagonalWeakLoadMinus_adjoint]
      _ = blockVecDot ((-pPlus, qPlus) : BlockVec d)
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (profileRecenteredMean P q g t)
                (blockDiag 1 (-1))))
            ((-pPlus, qPlus) : BlockVec d)) :=
        sq_diagonalWeakLoadMinus hEad hEadpd
      _ = _ := by rw [profileRecenteredAdjointMean_eq]
  rw [hload]
  rw [profileAdjointResponseDefect_identity hq hg hints hintt]
  change (1 / 2 : ℝ) * blockVecDot X
      (blockMatVecMul
        (blockSub (profileRecenteredAdjointMean P q g s)
          (profileRecenteredAdjointMean P q g t)) X) ≤ _
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [mul_assoc] using hscaled

end

end Homogenization.HighContrast.Response
