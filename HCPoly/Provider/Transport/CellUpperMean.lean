/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.GapFunctions
import HCPoly.Provider.Transport.NearIsometry

/-!
# The upper mean of a target cell

The transport reaches its target matrix through an upper comparison whose mean
is `K_W`, assembled from three pieces: the transport `S^t\overline P_WS` of the
convex combination of the selected cells, the correction `-(1-m_W)S^tS` for the
mass the selection leaves unfilled, and the mean `R_W` of the normalized source
residual, which the source rows bound by a multiple of `ε_j`.

This file proves the domination that opens the paragraph.  The correction is
subtracted from a positive matrix and can only help; the transported combination
is below `\widehat P_W = I + (S^t\overline P_WS - I)_+` because a symmetric
matrix never exceeds its own spectral positive part; and the residual
contributes its bound.  Hence

`K_W = S^t\overline P_WS - (1-m_W)S^tS + R_W ≤ \widehat P_W + Cε_jI`,

and, on traces, the trace gap of the upper mean exceeds that of the transported
combination by at most `2d` times the source bound.

The one matrix fact needed, that a symmetric matrix lies below its spectral
positive part, is read in the eigenbasis: both matrices are diagonal there and
the comparison is the scalar inequality `x ≤ max x 0` on each eigenvalue.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

/-! ## A symmetric matrix lies below its spectral positive part -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A symmetric matrix is below its spectral positive part.**  Read in the
eigenbasis both matrices are diagonal, and the comparison is the scalar
inequality `x ≤ max x 0` on each eigenvalue.  This is the matrix reading of the
positive-part order of a `C⋆`-algebra, in the unital functional calculus the
transport's positive part is written with. -/
theorem le_cfc_posPart {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    M ≤ cfc (fun x : ℝ => max x 0) M := by
  set U : Matrix n n ℝ := (hM.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  have hspec : M = U * Matrix.diagonal hM.eigenvalues * Uᴴ := by
    conv_lhs => rw [hM.spectral_theorem]
    simp [hUdef, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hform : cfc (fun x : ℝ => max x 0) M =
      U * Matrix.diagonal (fun i => max (hM.eigenvalues i) 0) * Uᴴ := by
    rw [hM.cfc_eq (fun x : ℝ => max x 0)]
    simp [Matrix.IsHermitian.cfc, hUdef, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def]
  refine Matrix.le_iff.mpr ?_
  have hdiff : cfc (fun x : ℝ => max x 0) M - M =
      U * Matrix.diagonal (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i) * Uᴴ := by
    have hrw : U * Matrix.diagonal (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i) * Uᴴ
        = U * Matrix.diagonal (fun i => max (hM.eigenvalues i) 0) * Uᴴ
          - U * Matrix.diagonal hM.eigenvalues * Uᴴ := by
      rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
    rw [hrw, ← hform, ← hspec]
  rw [hdiff]
  have hD : (Matrix.diagonal
      (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i)).PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    simp only [sub_nonneg]
    exact le_max_left _ _
  simpa [Matrix.conjTranspose_conjTranspose] using hD.conjTranspose_mul_mul_same Uᴴ

end Matrices

section Blocks

variable {d : ℕ}

/-! ## The domination of the upper mean -/

/-- The trace of a scalar multiple of the doubled identity. -/
private theorem trace_smul_one (c : ℝ) :
    Matrix.trace (c • (1 : FullBlockMat d)) = c * (2 * (d : ℝ)) := by
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  congr 1
  simp [Fintype.card_sum, two_mul]

/-- **The upper mean is dominated by the transported combination.**  The unfilled
mass is subtracted from a positive matrix, the transported combination is below
its own spectral positive part shifted by the identity, and the source residual
contributes its bound. -/
theorem upper_mean_domination {Pbar Mblk Phat KW Rm : BlockMat d} {S : FullBlockMat d}
    {mW eps : ℝ} (hmW : mW ≤ 1)
    (hPbar : (1 : FullBlockMat d) ≤ toFullBlockMat Pbar)
    (hR : toFullBlockMat Rm ≤ eps • (1 : FullBlockMat d))
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk))
    (hKW : toFullBlockMat KW =
      Sᵀ * toFullBlockMat Pbar * S - (1 - mW) • (Sᵀ * S) + toFullBlockMat Rm) :
    toFullBlockMat KW ≤ toFullBlockMat Phat + eps • (1 : FullBlockMat d) := by
  have hPps : (toFullBlockMat Pbar).PosSemidef := (posDef_of_one_le hPbar).posSemidef
  have hMherm : (toFullBlockMat Mblk).IsHermitian := by
    rw [hM]
    exact (posSemidef_transpose_conj hPps S).isHermitian.sub Matrix.isHermitian_one
  have hMle : toFullBlockMat Mblk ≤ toFullBlockMat (blockPosPart Mblk) := by
    rw [blockPosPart, toFullBlockMat_ofFullBlockMat]
    exact le_cfc_posPart hMherm
  have hgram : (0 : FullBlockMat d) ≤ (1 - mW) • (Sᵀ * S) :=
    Matrix.nonneg_iff_posSemidef.mpr
      ((posSemidef_transpose_mul_self S).smul (by linarith only [hmW]))
  have hconj : Sᵀ * toFullBlockMat Pbar * S - (1 - mW) • (Sᵀ * S) ≤
      toFullBlockMat Phat := by
    have hdrop : Sᵀ * toFullBlockMat Pbar * S - (1 - mW) • (Sᵀ * S) ≤
        Sᵀ * toFullBlockMat Pbar * S := sub_le_self _ hgram
    have hsplit : Sᵀ * toFullBlockMat Pbar * S = 1 + toFullBlockMat Mblk := by
      rw [hM]; abel
    rw [hPhat]
    exact hdrop.trans (le_of_eq_of_le hsplit (add_le_add le_rfl hMle))
  rw [hKW]
  exact add_le_add hconj hR

/-- **The trace form of the domination.**  A Loewner domination by a shifted
matrix compares the traces, the shift contributing `2d` times its scalar. -/
theorem blockTrace_le_of_upper_mean_domination {KW Phat : BlockMat d} {eps : ℝ}
    (h : toFullBlockMat KW ≤ toFullBlockMat Phat + eps • (1 : FullBlockMat d)) :
    blockTrace KW - 2 * (d : ℝ) ≤
      (blockTrace Phat - 2 * (d : ℝ)) + eps * (2 * (d : ℝ)) := by
  have hnn := (Matrix.le_iff.mp h).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_add, trace_smul_one] at hnn
  have hK : Matrix.trace (toFullBlockMat KW) = blockTrace KW := rfl
  have hP : Matrix.trace (toFullBlockMat Phat) = blockTrace Phat := rfl
  rw [hK, hP] at hnn
  linarith only [hnn]

end Blocks

end

end Transport
end HighContrast
end Homogenization
