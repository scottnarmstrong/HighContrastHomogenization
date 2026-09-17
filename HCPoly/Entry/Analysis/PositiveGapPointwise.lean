import HCPoly.Entry.Analysis.SchattenDiagonal
import Mathlib.Analysis.Matrix.Order

/-!
# Pointwise matrix inequalities for the PositiveGap support layer

This file keeps the deterministic block-matrix part separate from the later
random-field assembly.  The fixed block operations are used throughout.
-/

open Homogenization.HighContrast (blockSub blockTrace)
namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem toFullBlockMat_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

private theorem blockSub_eq_ofFullBlockMat_sub (A B : BlockMat d) :
    blockSub A B = ofFullBlockMat (toFullBlockMat A - toFullBlockMat B) := by
  cases A
  cases B
  rfl

private theorem blockLoewnerLE_to_matrixOrder {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) :
    toFullBlockMat A ≤ toFullBlockMat B := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
  intro q
  change 0 ≤ dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q)
  let X : BlockVec d := ofFullBlockVec q
  have hquad :
      dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q) =
        blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) := by
    rw [← dotProduct_toFullBlockVec X
      (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X)]
    rw [toFullBlockVec_blockMatVecMul]
    simp [X]
  have hdiff :
      blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
        blockVecDot X (blockMatVecMul B X) -
          blockVecDot X (blockMatVecMul A X) := by
    simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
  have horder := hAB X
  rw [hquad, hdiff]
  nlinarith

private theorem blockLoewnerLE_sub_posSemidef {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) :
    (toFullBlockMat (blockSub B A)).PosSemidef := by
  have horder := blockLoewnerLE_to_matrixOrder hA hB hAB
  rw [toFullBlockMat_blockSub]
  exact (Matrix.le_iff).mp horder

theorem ordered_gap_posSemidef {d : ℕ} {F G : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hG : IsSymmetricBlockMat G)
    (hFpos : BlockMatLoewnerLE (ofFullBlockMat 0) F)
    (hFG : BlockMatLoewnerLE F G) :
    (toFullBlockMat (blockSub G F)).PosSemidef ∧
      (toFullBlockMat G).PosSemidef ∧
      BlockMatLoewnerLE (blockSub G F) G := by
  let hFh : (toFullBlockMat F).IsHermitian := (toFullBlockMat_isHermitian_iff F).2 hF
  let hGh : (toFullBlockMat G).IsHermitian := (toFullBlockMat_isHermitian_iff G).2 hG
  have h0h : (toFullBlockMat (ofFullBlockMat (0 : FullBlockMat d))).IsHermitian := by
    simp
  have hFpsd : (toFullBlockMat F).PosSemidef := by
    convert blockLoewnerLE_sub_posSemidef h0h hFh hFpos using 1
    rw [toFullBlockMat_blockSub]
    simp
  have hDpsd : (toFullBlockMat (blockSub G F)).PosSemidef :=
    blockLoewnerLE_sub_posSemidef hFh hGh hFG
  have hGpsd : (toFullBlockMat G).PosSemidef := by
    have hsum : (toFullBlockMat F + toFullBlockMat (blockSub G F)).PosSemidef :=
      hFpsd.add hDpsd
    convert hsum using 1
    rw [toFullBlockMat_blockSub]
    ext α β
    simp
  refine ⟨hDpsd, hGpsd, ?_⟩
  intro X
  have hFquad :
      0 ≤ blockVecDot X (blockMatVecMul F X) := by
    have h := hFpsd.dotProduct_mulVec_nonneg (toFullBlockVec X)
    have h' :
        0 ≤ dotProduct (toFullBlockVec X)
          (Matrix.mulVec (toFullBlockMat F) (toFullBlockVec X)) := by
      simpa [dotProduct] using h
    rw [← toFullBlockVec_blockMatVecMul,
      dotProduct_toFullBlockVec X (blockMatVecMul F X)] at h'
    exact h'
  have hDquad :
      blockVecDot X (blockMatVecMul (blockSub G F) X) =
        blockVecDot X (blockMatVecMul G X) -
          blockVecDot X (blockMatVecMul F X) := by
    rw [blockSub_eq_ofFullBlockMat_sub G F]
    simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub G F X
  rw [hDquad]
  nlinarith

/-- Monotonicity of the real L2 operator norm on positive semidefinite blocks. -/
theorem blockOpNorm_mono_of_posSemidef {D G : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef)
    (hG : (toFullBlockMat G).IsHermitian) (hDG : BlockMatLoewnerLE D G) :
    blockOpNorm D ≤ blockOpNorm G := by
  have hdiff := (Matrix.le_iff).mp (blockLoewnerLE_to_matrixOrder hD.isHermitian hG hDG)
  let U := hD.isHermitian.eigenvectorUnitary
  have hdiag (i : BlockCoord d) : hD.isHermitian.eigenvalues i ≤
      (Unitary.conjStarAlgAut ℝ _ (star U) (toFullBlockMat G)) i i := by
    have hp := (hdiff.conjTranspose_mul_mul_same (U : FullBlockMat d)).diag_nonneg (i := i)
    have heq := hD.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    have hsub := map_sub (Unitary.conjStarAlgAut ℝ _ (star U))
      (toFullBlockMat G) (toFullBlockMat D)
    have hps : 0 ≤ (Unitary.conjStarAlgAut ℝ _ (star U)
        (toFullBlockMat G - toFullBlockMat D)) i i := hp
    rw [hsub, heq] at hps
    simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Function.comp_apply,
      RCLike.ofReal_real_eq_id, id_eq, sub_nonneg] using hps
  unfold blockOpNorm
  rw [hermitian_norm_eq_eigenvalue_norm hD.isHermitian]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [Real.norm_of_nonneg (hD.eigenvalues_nonneg i)]
  exact (hdiag i).trans (hermitian_conj_diagonal_le_norm hG (star U) i)

/-- The first display of the positive-gap proof, valid already for real `N ≥ 1`. -/
theorem absSchattenNorm_gap_le_opNorm_rpow_mul_trace_rpow {D G : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef)
    (hG : (toFullBlockMat G).IsHermitian) (hDG : BlockMatLoewnerLE D G)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N D ≤ blockOpNorm G ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have heig (i : BlockCoord d) : hD.isHermitian.eigenvalues i ≤ blockOpNorm G := by
    calc
      _ ≤ ‖hD.isHermitian.eigenvalues‖ := by
        simpa only [Real.norm_of_nonneg (hD.eigenvalues_nonneg i)] using
          norm_le_pi_norm hD.isHermitian.eigenvalues i
      _ = blockOpNorm D := (hermitian_norm_eq_eigenvalue_norm hD.isHermitian).symm
      _ ≤ blockOpNorm G := blockOpNorm_mono_of_posSemidef hD hG hDG
  have hsum : ∑ i, |hD.isHermitian.eigenvalues i| ^ N ≤
      blockOpNorm G ^ (N - 1) * blockTrace D := by
    rw [blockTrace, hD.isHermitian.trace_eq_sum_eigenvalues, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_of_nonneg (hD.eigenvalues_nonneg i)]
    calc
      _ = hD.isHermitian.eigenvalues i ^ (N - 1) * hD.isHermitian.eigenvalues i := by
        rw [← Real.rpow_add_one' (hD.eigenvalues_nonneg i)
          (by simpa only [sub_add_cancel] using hNpos.ne'), sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hD.eigenvalues_nonneg i) (heig i) (sub_nonneg.mpr hN))
        (hD.eigenvalues_nonneg i)
  rw [absSchattenNorm_eq_eigenvalues hD.isHermitian hN, schattenNormEigen]
  calc
    _ ≤ (blockOpNorm G ^ (N - 1) * blockTrace D) ^ N⁻¹ :=
      Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _))
        hsum (inv_nonneg.mpr hNpos.le)
    _ = _ := by
      unfold blockOpNorm
      rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg (toFullBlockMat G)) _) (blockTrace_nonneg hD),
        ← Real.rpow_mul (norm_nonneg (toFullBlockMat G))]
      congr 2
      field_simp [hNpos.ne']

/-- Sharp trace/Schatten comparison with the printed `2d` factor, including `d = 0`. -/
theorem trace_le_dim_rpow_mul_absSchattenNorm {D : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef) {N : ℝ} (hN : 1 ≤ N) :
    blockTrace D ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) * absSchattenNorm N D := by
  have hh := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hN
    (fun _ : BlockCoord d => (1 : ℝ)) hD.isHermitian.eigenvalues
    (fun _ => zero_le_one) hD.eigenvalues_nonneg
  rw [blockTrace, hD.isHermitian.trace_eq_sum_eigenvalues,
    absSchattenNorm_eq_eigenvalues hD.isHermitian hN, schattenNormEigen]
  simpa only [one_mul, abs_of_nonneg (hD.eigenvalues_nonneg _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, BlockCoord, Fintype.card_sum,
    Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ← two_mul] using! hh

/-- The trace interpolation used for the deterministic mean gap in the centering step. -/
theorem ordered_trace_le_dim_rpow_mul_opNorm_rpow_mul_trace_rpow {D G : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef)
    (hG : (toFullBlockMat G).IsHermitian) (hDG : BlockMatLoewnerLE D G)
    {N : ℝ} (hN : 1 ≤ N) :
    blockTrace D ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) *
      blockOpNorm G ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ := by
  calc
    _ ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) * absSchattenNorm N D :=
      trace_le_dim_rpow_mul_absSchattenNorm hD hN
    _ ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) *
        (blockOpNorm G ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹) :=
      mul_le_mul_of_nonneg_left (absSchattenNorm_gap_le_opNorm_rpow_mul_trace_rpow hD hG hDG hN)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := (mul_assoc _ _ _).symm

end

end Homogenization.HighContrast.Analysis
