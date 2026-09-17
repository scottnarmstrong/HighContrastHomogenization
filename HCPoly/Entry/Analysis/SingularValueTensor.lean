import HCPoly.Entry.Analysis.SingularValueMoments
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Tensor amplification of singular norms

Finite tensor products preserve matrix multiplication and multiply traces and
singular moments. All index types may be empty. In particular, the zeroth
tensor power is the identity on the singleton type `Fin 0 → n`.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Kronecker

noncomputable section

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The tensor power on a function index type, including the scalar zeroth power. -/
def tensorPower (X : Matrix n n ℝ) (q : ℕ) :
    Matrix (Fin q → n) (Fin q → n) ℝ := fun i j => ∏ k, X (i k) (j k)

omit [DecidableEq n] in
theorem tensorPower_mul (X Y : Matrix n n ℝ) (q : ℕ) :
    tensorPower (X * Y) q = tensorPower X q * tensorPower Y q := by
  ext i j
  simp only [tensorPower, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun k a => X (i k) a * Y a (j k))

omit [Fintype n] in
private theorem tensorPower_diagonal (d : n → ℝ) (q : ℕ) :
    tensorPower (Matrix.diagonal d) q = Matrix.diagonal (fun i => ∏ k, d (i k)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [tensorPower, Matrix.diagonal_apply_eq]
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Matrix.diagonal_apply_ne _ hk

omit [Fintype n] in
theorem tensorPower_one (q : ℕ) :
    tensorPower (1 : Matrix n n ℝ) q = 1 := by
  rw [← Matrix.diagonal_one, tensorPower_diagonal]
  simp only [Finset.prod_const_one, Matrix.diagonal_one]

omit [DecidableEq n] in
theorem trace_tensorPower (X : Matrix n n ℝ) (q : ℕ) :
    Matrix.trace (tensorPower X q) = Matrix.trace X ^ q := by
  exact (Fintype.sum_pow (fun i => X i i) q).symm

omit [Fintype n] [DecidableEq n] in
private theorem tensorPower_star (X : Matrix n n ℝ) (q : ℕ) :
    tensorPower (star X) q = star (tensorPower X q) := by
  ext i j
  simp only [tensorPower, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial]

private theorem sum_singularValues_of_diagonalization (X U : Matrix n n ℝ)
    (d : n → ℝ) (hU : star U * U = 1)
    (hX : star X * X = U * Matrix.diagonal d * star U) (f : ℝ → ℝ) :
    ∑ i, f (singularValues X i) = ∑ i, f (Real.sqrt (d i)) := by
  have hchar : (star X * X).charpoly = (Matrix.diagonal d).charpoly := by
    rw [hX, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, one_mul]
  have hroots : (star X * X).charpoly.roots = Finset.univ.val.map d := by
    rw [hchar, Matrix.charpoly_diagonal]
    simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using
      (Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map d))
  have h := congrArg (fun s : Multiset ℝ => (s.map (fun x => f (Real.sqrt x))).sum)
    ((Matrix.isHermitian_conjTranspose_mul_self X).roots_charpoly_eq_eigenvalues.symm.trans
      hroots)
  simpa only [singularValues, Multiset.map_map, Function.comp_def, Finset.sum,
    RCLike.ofReal_real_eq_id, id_eq] using h

private theorem gram_diagonalization (X : Matrix n n ℝ) :
    star X * X =
      (Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary *
        Matrix.diagonal (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues *
          star ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary :
            Matrix n n ℝ) := by
  simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id,
    Function.id_comp] using! (Matrix.isHermitian_conjTranspose_mul_self X).spectral_theorem

theorem singularNorm_tensorPower (X : Matrix n n ℝ) {p : ℝ} (hp : 0 < p)
    (q : ℕ) : singularNorm p (tensorPower X q) = singularNorm p X ^ q := by
  let U : Matrix n n ℝ := (Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary
  let d := (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hT : star (tensorPower U q) * tensorPower U q = 1 := by
    rw [← tensorPower_star, ← tensorPower_mul, hU, tensorPower_one]
  have hG : star (tensorPower X q) * tensorPower X q =
      tensorPower U q * Matrix.diagonal (fun i => ∏ k, d (i k)) *
        star (tensorPower U q) := by
    rw [← tensorPower_star, ← tensorPower_mul, gram_diagonalization X,
      tensorPower_mul, tensorPower_mul, tensorPower_diagonal, tensorPower_star]
  apply (Real.rpow_left_inj (singularNorm_nonneg _ _)
    (pow_nonneg (singularNorm_nonneg _ _) q) hp.ne').mp
  rw [singularNorm_rpow _ hp, ← Real.rpow_pow_comm (singularNorm_nonneg _ _),
    singularNorm_rpow _ hp]
  rw [sum_singularValues_of_diagonalization (tensorPower X q) (tensorPower U q) _ hT hG
    (fun x => x ^ p)]
  have hsqrt (i : Fin q → n) : Real.sqrt (∏ k, d (i k)) =
      ∏ k, singularValues X (i k) := by
    simp only [singularValues, Real.sqrt_eq_rpow]
    exact (Real.finsetProd_rpow _ _
      (fun k _ => Matrix.eigenvalues_conjTranspose_mul_self_nonneg X (i k)) _).symm
  simp_rw [hsqrt, ← Real.finsetProd_rpow _ _
    (fun k _ => singularValues_nonneg X _) p]
  exact (Fintype.sum_pow (fun i => singularValues X i ^ p) q).symm

theorem tensorPower_prod {N : ℕ} (A : Fin N → Matrix n n ℝ) (q : ℕ) :
    tensorPower ((List.ofFn A).prod) q = (List.ofFn fun k => tensorPower (A k) q).prod := by
  let F : Matrix n n ℝ →* Matrix (Fin q → n) (Fin q → n) ℝ :=
    { toFun := fun X => tensorPower X q
      map_one' := tensorPower_one q
      map_mul' := fun X Y => tensorPower_mul X Y q }
  simpa only [List.map_ofFn, Function.comp_def] using! ((List.ofFn A).prod_hom F).symm

end

end Homogenization.HighContrast.Analysis
