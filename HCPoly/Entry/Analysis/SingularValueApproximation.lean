import HCPoly.Entry.Analysis.SingularValues
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Approximation by matrices of bounded rank

The decreasing singular values, padded by zero, characterize approximation
in the L2 operator norm. All statements allow an empty index type.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The decreasing singular values, indexed from zero and padded by zero. -/
def singularValueAt (X : Matrix n n ℝ) (r : ℕ) : ℝ :=
  if h : r < Fintype.card n then singularValues₀ X ⟨r, h⟩ else 0

theorem singularValueAt_nonneg (X : Matrix n n ℝ) (r : ℕ) :
    0 ≤ singularValueAt X r := by
  unfold singularValueAt
  split
  · exact singularValues₀_nonneg X _
  · exact le_rfl

theorem singularValueAt_antitone (X : Matrix n n ℝ) : Antitone (singularValueAt X) := by
  intro i j hij
  by_cases hj : j < Fintype.card n
  · have hi := lt_of_le_of_lt hij hj
    simp only [singularValueAt, dif_pos hi, dif_pos hj]
    exact singularValues₀_antitone X hij
  · simp only [singularValueAt, dif_neg hj]
    split
    · exact singularValues₀_nonneg X _
    · exact le_rfl

theorem singularValueAt_eq_zero (X : Matrix n n ℝ) {r : ℕ}
    (hr : Fintype.card n ≤ r) : singularValueAt X r = 0 := by
  exact dif_neg (not_lt_of_ge hr)

omit [DecidableEq n] in
theorem rank_add_le (X Y : Matrix n n ℝ) : (X + Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le X.mulVecLin Y.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem gram_diagonal (X : Matrix n n ℝ) :
    star (X * (isHermitian_conjTranspose_mul_self X).eigenvectorUnitary) *
        (X * (isHermitian_conjTranspose_mul_self X).eigenvectorUnitary) =
      diagonal (isHermitian_conjTranspose_mul_self X).eigenvalues := by
  simpa only [Unitary.conjStarAlgAut_star_apply, StarMul.star_mul, Matrix.mul_assoc,
    RCLike.ofReal_real_eq_id, Function.id_comp] using!
    (isHermitian_conjTranspose_mul_self X).conjStarAlgAut_star_eigenvectorUnitary

omit [DecidableEq n] in
private theorem dot_mulVec_self (A : Matrix n n ℝ) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ ((star A * A) *ᵥ v) := by
  symm
  rw [← mulVec_mulVec, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, dotProduct_mulVec, vecMul_transpose]

private theorem dot_gram_coordinates (X : Matrix n n ℝ) (v : n → ℝ) :
    ((X * ((isHermitian_conjTranspose_mul_self X).eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v) ⬝ᵥ
        ((X * ((isHermitian_conjTranspose_mul_self X).eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v) =
      ∑ i, (isHermitian_conjTranspose_mul_self X).eigenvalues i * v i ^ 2 := by
  rw [dot_mulVec_self, gram_diagonal]
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem dot_mulVec_le (A : Matrix n n ℝ) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ ‖A‖ ^ 2 * (v ⬝ᵥ v) := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm (WithLp.toLp 2 v)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 h
  rw [Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  simp only [Real.norm_eq_abs] at hs
  simp only [sq_abs] at hs
  simpa only [dotProduct, pow_two] using hs

private theorem exists_supported_kernel (B : Matrix n n ℝ)
    (e : n ≃ Fin (Fintype.card n)) (r : ℕ) (hr : r < Fintype.card n)
    (hB : B.rank ≤ r) :
    ∃ v : n → ℝ, v ≠ 0 ∧ B *ᵥ v = 0 ∧ ∀ i, r < (e i).val → v i = 0 := by
  let f : Fin (r + 1) → n := fun j => e.symm ⟨j.val, lt_of_lt_of_le j.isLt hr⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    simpa only [f, Equiv.apply_symm_apply] using congrArg (fun k => (e k).val) hij
  let J : Matrix n (Fin (r + 1)) ℝ := fun i j => if i = f j then 1 else 0
  have hJ (w : Fin (r + 1) → ℝ) (j : Fin (r + 1)) : (J *ᵥ w) (f j) = w j := by
    simp only [J, mulVec, dotProduct, hf.eq_iff, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hdim := (B * J).mulVecLin.finrank_range_add_finrank_ker
  have hCJ : (B * J).rank ≤ r := (Matrix.rank_mul_le_left B J).trans hB
  have hker : LinearMap.ker (B * J).mulVecLin ≠ ⊥ := by
    apply Submodule.one_le_finrank_iff.mp
    change (B * J).rank + Module.finrank ℝ (LinearMap.ker (B * J).mulVecLin) =
      Module.finrank ℝ (Fin (r + 1) → ℝ) at hdim
    rw [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨J *ᵥ w, ?_, ?_, ?_⟩
  · intro hzero
    apply hw0
    funext j
    have h := congrFun hzero (f j)
    simpa only [hJ, Pi.zero_apply] using h
  · rw [mulVec_mulVec]
    exact hw
  · intro i hi
    change ∑ j, J i j * w j = 0
    apply Finset.sum_eq_zero
    intro j _
    have hij : i ≠ f j := by
      intro h
      have hv : (e i).val = j.val := by
        simpa only [f, Equiv.apply_symm_apply] using congrArg (fun k => (e k).val) h
      omega
    simp only [J, if_neg hij, zero_mul]

private theorem norm_gram_diagonal (X : Matrix n n ℝ) (a : n → ℝ) :
    ‖X * (isHermitian_conjTranspose_mul_self X).eigenvectorUnitary * diagonal a‖ ^ 2 =
      ‖fun i => (isHermitian_conjTranspose_mul_self X).eigenvalues i * a i ^ 2‖ := by
  let Y := X * ((isHermitian_conjTranspose_mul_self X).eigenvectorUnitary : Matrix n n ℝ)
  have hgram : star (Y * diagonal a) * (Y * diagonal a) =
      diagonal (fun i => (isHermitian_conjTranspose_mul_self X).eigenvalues i * a i ^ 2) := by
    rw [StarMul.star_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (star (diagonal a)),
      gram_diagonal]
    simp only [Matrix.star_eq_conjTranspose, diagonal_conjTranspose, star_trivial,
      diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [pow_two, ← CStarRing.norm_star_mul_self, hgram, Matrix.l2_opNorm_diagonal]

private theorem singularValueAt_sq (X : Matrix n n ℝ) {r : ℕ}
    (hr : r < Fintype.card n) :
    singularValueAt X r ^ 2 = (isHermitian_conjTranspose_mul_self X).eigenvalues₀ ⟨r, hr⟩ := by
  let e : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have h := Matrix.eigenvalues_conjTranspose_mul_self_nonneg X (e.symm ⟨r, hr⟩)
  change 0 ≤ (isHermitian_conjTranspose_mul_self X).eigenvalues₀ (e (e.symm ⟨r, hr⟩)) at h
  rw [Equiv.apply_symm_apply] at h
  simpa only [singularValueAt, dif_pos hr, singularValues₀] using Real.sq_sqrt h

theorem singularValueAt_le_norm_sub (X R : Matrix n n ℝ) {r : ℕ}
    (hR : R.rank ≤ r) : singularValueAt X r ≤ ‖X - R‖ := by
  by_cases hr : r < Fintype.card n
  · let hG := isHermitian_conjTranspose_mul_self X
    let U := hG.eigenvectorUnitary
    let e : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    obtain ⟨v, hv0, hvR, hv⟩ := exists_supported_kernel
      (R * (U : Matrix n n ℝ)) e r hr
      ((Matrix.rank_mul_le_left R (U : Matrix n n ℝ)).trans hR)
    have hvpos : 0 < v ⬝ᵥ v := by
      exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
        (fun h => hv0 (dotProduct_self_eq_zero.mp h.symm))
    have hlow : singularValueAt X r ^ 2 * (v ⬝ᵥ v) ≤
        ((X * (U : Matrix n n ℝ)) *ᵥ v) ⬝ᵥ ((X * (U : Matrix n n ℝ)) *ᵥ v) := by
      rw [dot_gram_coordinates, singularValueAt_sq X hr]
      simp only [dotProduct, Finset.mul_sum, ← pow_two]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : r < (e i).val
      · simp only [hv i hi, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
      · exact mul_le_mul_of_nonneg_right
          (hG.eigenvalues₀_antitone (show e i ≤ ⟨r, hr⟩ from Nat.le_of_not_gt hi)) (sq_nonneg _)
    have hnorm := dot_mulVec_le ((X - R) * (U : Matrix n n ℝ)) v
    rw [CStarRing.norm_mul_coe_unitary, Matrix.sub_mul, Matrix.sub_mulVec, hvR, sub_zero] at hnorm
    exact (sq_le_sq₀ (singularValueAt_nonneg X r) (norm_nonneg _)).1
      ((mul_le_mul_iff_left₀ hvpos).1 (hlow.trans hnorm))
  · rw [singularValueAt_eq_zero X (Nat.le_of_not_gt hr)]
    exact norm_nonneg _

theorem exists_rank_approximation (X : Matrix n n ℝ) (r : ℕ) :
    ∃ R : Matrix n n ℝ, R.rank ≤ r ∧ ‖X - R‖ ≤ singularValueAt X r := by
  classical
  by_cases hr : r < Fintype.card n
  · let hG := isHermitian_conjTranspose_mul_self X
    let U := hG.eigenvectorUnitary
    let e : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    let a : n → ℝ := fun i => if (e i).val < r then 1 else 0
    let b : n → ℝ := fun i => if (e i).val < r then 0 else 1
    have ha_rank : (diagonal a).rank ≤ r := by
      rw [Matrix.rank_diagonal]
      have ha (i : {i // a i ≠ 0}) : (e i.val).val < r := by
        by_contra hi
        exact i.prop (if_neg hi)
      let f : {i // a i ≠ 0} → Fin r := fun i => ⟨(e i.val).val, ha i⟩
      have hf : Function.Injective f := by
        intro i j hij
        apply Subtype.ext
        apply e.injective
        apply Fin.ext
        exact congrArg (fun k : Fin r => k.val) hij
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    refine ⟨X * (U : Matrix n n ℝ) * diagonal a * star (U : Matrix n n ℝ), ?_, ?_⟩
    · exact (Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_mul_le_right _ _).trans ha_rank)
    · have hdiag : diagonal b = 1 - diagonal a := by
        rw [← diagonal_one, diagonal_sub]
        congr 1
        funext i
        dsimp [a, b]
        split <;> norm_num
      have hres : X - X * (U : Matrix n n ℝ) * diagonal a * star (U : Matrix n n ℝ) =
          X * (U : Matrix n n ℝ) * diagonal b * star (U : Matrix n n ℝ) := by
        have hU : X * (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = X := by
          rw [Matrix.mul_assoc, Unitary.mul_star_self_of_mem U.prop, mul_one]
        rw [hdiag, mul_sub, mul_one, sub_mul, hU]
      rw [hres, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop)]
      apply (sq_le_sq₀ (norm_nonneg _) (singularValueAt_nonneg X r)).1
      rw [norm_gram_diagonal, singularValueAt_sq X hr]
      apply (pi_norm_le_iff_of_nonneg ?_).2
      · intro i
        by_cases hi : (e i).val < r
        · simp only [b, if_pos hi, zero_pow (by decide : 2 ≠ 0), mul_zero, norm_zero]
          rw [← singularValueAt_sq X hr]
          exact sq_nonneg _
        · simp only [b, if_neg hi, one_pow, mul_one]
          rw [Real.norm_of_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg X i)]
          exact hG.eigenvalues₀_antitone (show (⟨r, hr⟩ : Fin (Fintype.card n)) ≤ e i from
            Nat.le_of_not_gt hi)
      · rw [← singularValueAt_sq X hr]
        exact sq_nonneg _
  · refine ⟨X, (Matrix.rank_le_card_width X).trans (Nat.le_of_not_gt hr), ?_⟩
    rw [sub_self, norm_zero]
    exact singularValueAt_nonneg X r

end

end Homogenization.HighContrast.Analysis
