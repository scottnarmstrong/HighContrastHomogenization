import HCPoly.Entry.Analysis.SchattenSpectral
import Mathlib.Analysis.MeanInequalities

/-!
# Diagonal estimates in orthogonal bases

Squared entries of a real unitary matrix have row and column sums one. Weighted
scalar Hölder therefore bounds the diagonal in any orthogonal basis by the
spectral Schatten value. No commutation of the matrices is used.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem unitary_sum_sq_row (U : unitary (Matrix n n ℝ)) (i : n) :
    ∑ j, (U : Matrix n n ℝ) i j ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (Unitary.coe_mul_star_self U)
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
    pow_two] using! h

theorem unitary_sum_sq_col (U : unitary (Matrix n n ℝ)) (j : n) :
    ∑ i, (U : Matrix n n ℝ) i j ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M j j) (Unitary.coe_star_mul_self U)
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
    pow_two] using h

theorem unitary_conj_diagonal_apply (U : unitary (Matrix n n ℝ)) (f : n → ℝ) (i : n) :
    (Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal f)) i i =
      ∑ j, (U : Matrix n n ℝ) i j ^ 2 * f j := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hermitian_conj_diagonal_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℝ)) (i : n) :
    (Unitary.conjStarAlgAut ℝ _ U A) i i =
      ∑ j, ((U * hA.eigenvectorUnitary : unitary (Matrix n n ℝ)) : Matrix n n ℝ) i j ^ 2 *
        hA.eigenvalues j := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← Unitary.conjStarAlgAut_mul_apply]
  exact unitary_conj_diagonal_apply _ _ i

theorem hermitian_norm_eq_eigenvalue_norm {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply,
    CStarRing.norm_mul_mem_unitary (hU := Unitary.star_mem hA.eigenvectorUnitary.prop),
    CStarRing.norm_mem_unitary_mul _ hA.eigenvectorUnitary.prop]
  change ‖Matrix.diagonal hA.eigenvalues‖ = ‖hA.eigenvalues‖
  exact Matrix.l2_opNorm_diagonal _

theorem hermitian_conj_diagonal_le_norm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℝ)) (i : n) :
    (Unitary.conjStarAlgAut ℝ _ U A) i i ≤ ‖A‖ := by
  rw [hermitian_conj_diagonal_eq hA U i, hermitian_norm_eq_eigenvalue_norm hA]
  calc
    _ ≤ ∑ j, ((U * hA.eigenvectorUnitary : unitary (Matrix n n ℝ)) : Matrix n n ℝ) i j ^ 2 *
        ‖hA.eigenvalues‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm hA.eigenvalues j))) (sq_nonneg _)
    _ = ‖hA.eigenvalues‖ := by
      rw [← Finset.sum_mul, unitary_sum_sq_row, one_mul]

theorem unitary_diagonal_rpow_le (U : unitary (Matrix n n ℝ)) (f : n → ℝ)
    {N : ℝ} (hN : 1 ≤ N) (i : n) :
    |∑ j, (U : Matrix n n ℝ) i j ^ 2 * f j| ^ N ≤
      ∑ j, (U : Matrix n n ℝ) i j ^ 2 * |f j| ^ N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have habs : |∑ j, (U : Matrix n n ℝ) i j ^ 2 * f j| ≤
      ∑ j, (U : Matrix n n ℝ) i j ^ 2 * |f j| := by
    calc
      _ ≤ ∑ j, |(U : Matrix n n ℝ) i j ^ 2 * f j| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_pow, sq_abs]
  have hh := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hN
    (fun j => (U : Matrix n n ℝ) i j ^ 2) (fun j => |f j|)
    (fun _ => sq_nonneg _) (fun _ => abs_nonneg _)
  rw [unitary_sum_sq_row, Real.one_rpow, one_mul] at hh
  have hr := Real.rpow_le_rpow (abs_nonneg _) (habs.trans hh) hNpos.le
  rwa [Real.rpow_inv_rpow (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _))) hNpos.ne'] at hr

theorem hermitian_sum_diagonal_rpow_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℝ)) {N : ℝ} (hN : 1 ≤ N) :
    ∑ i, |(Unitary.conjStarAlgAut ℝ _ U A) i i| ^ N ≤
      ∑ j, |hA.eigenvalues j| ^ N := by
  calc
    _ ≤ ∑ i, ∑ j,
        ((U * hA.eigenvectorUnitary : unitary (Matrix n n ℝ)) : Matrix n n ℝ) i j ^ 2 *
          |hA.eigenvalues j| ^ N := by
      apply Finset.sum_le_sum
      intro i _
      rw [hermitian_conj_diagonal_eq]
      exact unitary_diagonal_rpow_le _ _ hN i
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, unitary_sum_sq_col, one_mul]

end

end Homogenization.HighContrast.Analysis
