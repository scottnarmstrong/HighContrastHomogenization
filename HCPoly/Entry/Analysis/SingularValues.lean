import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Singular values and the trace bound

Singular values of a real square matrix are square roots of its Gram
eigenvalues. `singularValues` uses the original index type, without an order
claim; `singularValues₀` uses Mathlib's decreasing eigenvalue enumeration.
The trace bound uses a Gram eigenbasis and scalar Cauchy–Schwarz, so it
also applies to singular matrices and empty index types.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Singular values indexed by the original matrix index type, without an ordering claim. -/
def singularValues (X : Matrix n n ℝ) (i : n) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)

/-- Singular values in decreasing order, indexed from zero. -/
def singularValues₀ (X : Matrix n n ℝ) (i : Fin (Fintype.card n)) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues₀ i)

theorem singularValues_nonneg (X : Matrix n n ℝ) (i : n) :
    0 ≤ singularValues X i := Real.sqrt_nonneg _

theorem singularValues₀_nonneg (X : Matrix n n ℝ) (i : Fin (Fintype.card n)) :
    0 ≤ singularValues₀ X i := Real.sqrt_nonneg _

theorem singularValues₀_antitone (X : Matrix n n ℝ) : Antitone (singularValues₀ X) := by
  intro i j hij
  exact Real.sqrt_le_sqrt
    ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues₀_antitone hij)

theorem sum_singularValues₀ (X : Matrix n n ℝ) (f : ℝ → ℝ) :
    ∑ i, f (singularValues₀ X i) = ∑ i, f (singularValues X i) := by
  let e : n ≃ Fin (Fintype.card n) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  exact (e.sum_comp (fun i => f (singularValues₀ X i))).symm

private theorem sum_sq_col_unitary (U : Matrix.unitaryGroup n ℝ) (i : n) :
    ∑ j, (U : Matrix n n ℝ) j i ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (Unitary.coe_star_mul_self U)
  simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial, Matrix.one_apply_eq, pow_two] using h

private theorem sum_sq_col_mul_gram_unitary (X : Matrix n n ℝ) (i : n) :
    ∑ j, (X * (Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary) j i ^ 2 =
      (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self X
  let U := hG.eigenvectorUnitary
  have hdiag : star (X * (U : Matrix n n ℝ)) * (X * (U : Matrix n n ℝ)) =
      Matrix.diagonal hG.eigenvalues := by
    have h := hG.conjStarAlgAut_star_eigenvectorUnitary
    simpa only [Unitary.conjStarAlgAut_star_apply, star_mul, Matrix.mul_assoc,
      RCLike.ofReal_real_eq_id, Function.id_comp] using! h
  have h := congrArg (fun M : Matrix n n ℝ => M i i) hdiag
  simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial, Matrix.diagonal_apply_eq, pow_two] using h

theorem abs_trace_le_sum_singularValues (X : Matrix n n ℝ) :
    |Matrix.trace X| ≤ ∑ i, singularValues X i := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self X
  let U := hG.eigenvectorUnitary
  have htrace : Matrix.trace (star (U : Matrix n n ℝ) * X * (U : Matrix n n ℝ)) =
      Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, Unitary.mul_star_self_of_mem U.prop, one_mul]
  rw [← htrace, Matrix.trace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => (U : Matrix n n ℝ) j i) (fun j => (X * (U : Matrix n n ℝ)) j i)
  rw [sum_sq_col_unitary U i, one_mul, sum_sq_col_mul_gram_unitary X i] at hcs
  have hentry : (star (U : Matrix n n ℝ) * X * (U : Matrix n n ℝ)) i i =
      ∑ j, (U : Matrix n n ℝ) j i * (X * (U : Matrix n n ℝ)) j i := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial]
  change |(star (U : Matrix n n ℝ) * X * (U : Matrix n n ℝ)) i i| ≤ singularValues X i
  rw [hentry]
  calc
    |∑ j, (U : Matrix n n ℝ) j i * (X * (U : Matrix n n ℝ)) j i| =
        Real.sqrt ((∑ j, (U : Matrix n n ℝ) j i * (X * (U : Matrix n n ℝ)) j i) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ singularValues X i := Real.sqrt_le_sqrt hcs

theorem abs_trace_le_sum_singularValues₀ (X : Matrix n n ℝ) :
    |Matrix.trace X| ≤ ∑ i, singularValues₀ X i := by
  rw [sum_singularValues₀ X (fun x => x)]
  exact abs_trace_le_sum_singularValues X

end

end Homogenization.HighContrast.Analysis
