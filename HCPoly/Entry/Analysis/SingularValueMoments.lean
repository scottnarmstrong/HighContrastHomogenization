import HCPoly.Entry.Analysis.SingularValues
import HCPoly.Entry.Analysis.SchattenSpectral

/-!
# Singular moments and the Schatten norm

For a Hermitian matrix, the singular-value multiset is the absolute-value
eigenvalue multiset. The proof compares characteristic polynomials; it does
not assert that the two enumerations have the same order. The resulting
moment identity identifies the generic singular norm with the
Schatten norm on its intended Hermitian domain.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The singular p-norm of an arbitrary real square matrix. Norm identities
below require a positive exponent; no norm interpretation is asserted at p=0. -/
def singularNorm (p : ℝ) (X : Matrix n n ℝ) : ℝ :=
  (∑ i, singularValues X i ^ p) ^ p⁻¹

theorem sum_eigenvalues_cfc {X : Matrix n n ℝ} (hX : X.IsHermitian)
    (f g : ℝ → ℝ) (hf : (cfc f X).IsHermitian) :
    ∑ i, g (hf.eigenvalues i) = ∑ i, g (f (hX.eigenvalues i)) := by
  have hroots : (cfc f X).charpoly.roots =
      Finset.univ.val.map (fun i => f (hX.eigenvalues i)) := by
    rw [hX.charpoly_cfc_eq]
    simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using!
      (Polynomial.roots_multiset_prod_X_sub_C
        (Finset.univ.val.map (fun i => f (hX.eigenvalues i))))
  have h := congrArg (fun s : Multiset ℝ => (s.map g).sum)
    (hf.roots_charpoly_eq_eigenvalues.symm.trans hroots)
  simpa only [Multiset.map_map, Function.comp_def, Finset.sum] using! h

theorem sum_singularValues_eq_abs_eigenvalues {X : Matrix n n ℝ}
    (hX : X.IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f (singularValues X i) = ∑ i, f |hX.eigenvalues i| := by
  have hGram : X.conjTranspose * X = cfc (fun x : ℝ => x ^ (2 : ℕ)) X := by
    calc
      X.conjTranspose * X = X ^ (2 : ℕ) := by rw [hX.eq, pow_two]
      _ = _ := (cfc_pow_id (R := ℝ) (a := X) (n := 2) (ha := hX)).symm
  have hG := Matrix.isHermitian_conjTranspose_mul_self X
  have hf : (cfc (fun x : ℝ => x ^ (2 : ℕ)) X).IsHermitian := hGram ▸ hG
  have h := sum_eigenvalues_cfc hX (fun x => x ^ (2 : ℕ)) (fun x => f (Real.sqrt x)) hf
  simp only [Real.sqrt_sq_eq_abs] at h
  rw [← h]
  unfold singularValues
  congr 1
  funext i
  congr 2
  exact congrFun ((hG.eigenvalues_eq_eigenvalues_iff hf).2
    (congrArg Matrix.charpoly hGram)) i

theorem singularNorm_nonneg (p : ℝ) (X : Matrix n n ℝ) : 0 ≤ singularNorm p X :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg X i) p) _

theorem singularNorm_rpow (X : Matrix n n ℝ) {p : ℝ} (hp : 0 < p) :
    singularNorm p X ^ p = ∑ i, singularValues X i ^ p := by
  exact Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg X i) p) hp.ne'

theorem singularNorm_eq_absSchattenNorm {d : ℕ} {A : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) {p : ℝ} (hp : 1 ≤ p) :
    singularNorm p (toFullBlockMat A) = absSchattenNorm p A := by
  rw [singularNorm, sum_singularValues_eq_abs_eigenvalues hA (fun x => x ^ p),
    absSchattenNorm_eq_eigenvalues hA hp, schattenNormEigen]

end

end Homogenization.HighContrast.Analysis
