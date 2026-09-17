import HCPoly.Entry.Analysis.SchattenDiagonal

/-!
# The Schatten triangle inequality for symmetric real blocks

Diagonalize the sum, apply scalar Minkowski to its diagonal entries, and bound
the diagonal of each summand by weighted Hölder. This proves coefficient one
for noncommuting signed symmetric matrices and every real exponent `N ≥ 1`.
-/

open Homogenization.HighContrast (blockSub)
namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem absSchattenNorm_diagonal_root_le {A : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (U : unitary (FullBlockMat d))
    {N : ℝ} (hN : 1 ≤ N) :
    (∑ i, |(Unitary.conjStarAlgAut ℝ _ U (toFullBlockMat A)) i i| ^ N) ^ N⁻¹ ≤
      absSchattenNorm N A := by
  rw [absSchattenNorm_eq_eigenvalues hA hN, schattenNormEigen]
  exact Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ =>
    Real.rpow_nonneg (abs_nonneg _) _)) (hermitian_sum_diagonal_rpow_le hA U hN)
    (inv_nonneg.mpr (le_trans zero_le_one hN))

/-- Full triangle inequality, including the trace-norm endpoint and empty blocks. -/
theorem absSchattenNorm_add_le {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) ≤
      absSchattenNorm N A + absSchattenNorm N B := by
  let U := star (hA.add hB).eigenvectorUnitary
  let T := Unitary.conjStarAlgAut ℝ (FullBlockMat d) U
  have heq (i : BlockCoord d) :
      (hA.add hB).eigenvalues i =
        T (toFullBlockMat A) i i + T (toFullBlockMat B) i i := by
    have hh := congrArg (fun M : FullBlockMat d => M i i)
      (hA.add hB).conjStarAlgAut_star_eigenvectorUnitary
    change T (toFullBlockMat A + toFullBlockMat B) i i = _ at hh
    rw [map_add] at hh
    simpa only [Matrix.diagonal_apply_eq, Matrix.add_apply, Function.comp_apply,
      RCLike.ofReal_real_eq_id, id_eq] using hh.symm
  have hsum : absSchattenNorm N (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) =
      (∑ i, |T (toFullBlockMat A) i i + T (toFullBlockMat B) i i| ^ N) ^ N⁻¹ := by
    have hAB : (toFullBlockMat (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B))).IsHermitian := by
      simpa only [toFullBlockMat_ofFullBlockMat] using hA.add hB
    rw [absSchattenNorm_eq_eigenvalues hAB hN, schattenNormEigen]
    simp only [toFullBlockMat_ofFullBlockMat]
    change (∑ i, |(hA.add hB).eigenvalues i| ^ N) ^ N⁻¹ = _
    simp only [heq]
  rw [hsum]
  calc
    _ ≤ (∑ i, |T (toFullBlockMat A) i i| ^ N) ^ N⁻¹ +
        (∑ i, |T (toFullBlockMat B) i i| ^ N) ^ N⁻¹ := by
      simpa only [one_div] using Real.Lp_add_le Finset.univ
        (fun i => T (toFullBlockMat A) i i) (fun i => T (toFullBlockMat B) i i) hN
    _ ≤ _ := add_le_add (absSchattenNorm_diagonal_root_le hA U hN)
      (absSchattenNorm_diagonal_root_le hB U hN)

/-- Invariance under negation, obtained by applying the diagonal estimate twice. -/
theorem absSchattenNorm_neg {A : BlockMat d} (hA : (toFullBlockMat A).IsHermitian)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (ofFullBlockMat (-toFullBlockMat A)) = absSchattenNorm N A := by
  have hneg : (toFullBlockMat (ofFullBlockMat (-toFullBlockMat A))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat] using hA.neg
  have aux {B : BlockMat d} (hB : (toFullBlockMat B).IsHermitian) :
      absSchattenNorm N (ofFullBlockMat (-toFullBlockMat B)) ≤ absSchattenNorm N B := by
    let hn : (-toFullBlockMat B).IsHermitian := hB.neg
    let U := star hn.eigenvectorUnitary
    have hh := absSchattenNorm_diagonal_root_le hB U hN
    have heq (i : BlockCoord d) :
        |(Unitary.conjStarAlgAut ℝ _ U (toFullBlockMat B)) i i| = |hn.eigenvalues i| := by
      have he := congrArg (fun M : FullBlockMat d => M i i)
        hn.conjStarAlgAut_star_eigenvectorUnitary
      rw [map_neg] at he
      simp only [Matrix.neg_apply, Matrix.diagonal_apply_eq, Function.comp_apply,
        RCLike.ofReal_real_eq_id, id_eq] at he
      rw [← he, abs_neg]
    simp only [heq] at hh
    have hn' : (toFullBlockMat (ofFullBlockMat (-toFullBlockMat B))).IsHermitian := by
      simpa only [toFullBlockMat_ofFullBlockMat] using hn
    rw [absSchattenNorm_eq_eigenvalues hn' hN, schattenNormEigen]
    simpa only [toFullBlockMat_ofFullBlockMat] using hh
  apply le_antisymm (aux hA)
  simpa only [toFullBlockMat_ofFullBlockMat, neg_neg, ofFullBlockMat_toFullBlockMat] using aux hneg

/-- Subtraction form consumed by the centering step. -/
theorem absSchattenNorm_sub_le {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (blockSub A B) ≤ absSchattenNorm N A + absSchattenNorm N B := by
  have hn : (toFullBlockMat (ofFullBlockMat (-toFullBlockMat B))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat] using hB.neg
  have hh := absSchattenNorm_add_le hA hn hN
  rw [absSchattenNorm_neg hB hN, toFullBlockMat_ofFullBlockMat, ← sub_eq_add_neg] at hh
  have heq : blockSub A B = ofFullBlockMat (toFullBlockMat A - toFullBlockMat B) := by
    cases A
    cases B
    rfl
  rwa [heq]

end

end Homogenization.HighContrast.Analysis
