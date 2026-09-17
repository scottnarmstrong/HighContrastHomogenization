import HCPoly.Entry.Setup.SchattenNorm
import Homogenization.Ambient.BlockMatrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Spectral facts for the Schatten norm

This file discharges the deterministic spectral bridge for the real-valued
Schatten norm of `HCPoly/Entry/Setup/SchattenNorm.lean`.
-/

open Homogenization.HighContrast (blockTrace)
namespace Homogenization.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

theorem toFullBlockMat_isHermitian_iff (H : BlockMat d) :
    (toFullBlockMat H).IsHermitian ↔ IsSymmetricBlockMat H := by
  constructor
  · intro hH α β
    have h := congrFun (congrFun hH.eq β) α
    cases α <;> cases β <;>
      simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply] using h
  · intro hH
    change Matrix.conjTranspose (toFullBlockMat H) = toFullBlockMat H
    ext α β
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inl i) (Sum.inl j)).symm
        | inr j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inl i) (Sum.inr j)).symm
    | inr i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inr i) (Sum.inl j)).symm
        | inr j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inr i) (Sum.inr j)).symm

private theorem trace_cfc_eq_sum {H : BlockMat d} (hH : (toFullBlockMat H).IsHermitian)
    (f : ℝ → ℝ) :
    Matrix.trace (cfc f (toFullBlockMat H)) = ∑ i, f (hH.eigenvalues i) := by
  rw [hH.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rfl

theorem trace_cfc_abs_rpow_eq_sum {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (_hN : 1 ≤ N) :
    Matrix.trace (cfc (fun x : ℝ => |x| ^ N) (toFullBlockMat H)) =
      ∑ i, |hH.eigenvalues i| ^ N := by
  exact trace_cfc_eq_sum hH (fun x : ℝ => |x| ^ N)

theorem absSchattenNorm_eq_eigenvalues {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (_hN : 1 ≤ N) :
    absSchattenNorm N H = schattenNormEigen hH N := by
  unfold absSchattenNorm schattenNormEigen
  rw [trace_cfc_abs_rpow_eq_sum hH (N := N) (by assumption)]

private theorem eigenvalue_abs_rpow_sum_nonneg {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (N : ℝ) :
    0 ≤ ∑ i, |hH.eigenvalues i| ^ N :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) N

theorem absSchattenNorm_nonneg {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    0 ≤ absSchattenNorm N H := by
  rw [absSchattenNorm_eq_eigenvalues hH hN, schattenNormEigen]
  exact Real.rpow_nonneg (eigenvalue_abs_rpow_sum_nonneg hH N) N⁻¹

theorem absSchattenNorm_rpow_eq_sum {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N H ^ N = ∑ i, |hH.eigenvalues i| ^ N := by
  rw [absSchattenNorm_eq_eigenvalues hH hN, schattenNormEigen]
  exact Real.rpow_inv_rpow (eigenvalue_abs_rpow_sum_nonneg hH N)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))

private theorem abs_pow_even_two_mul (x : ℝ) (k : ℕ) :
    |x| ^ (2 * k : ℕ) = x ^ (2 * k : ℕ) := by
  by_cases hx : 0 ≤ x
  · simp [abs_of_nonneg hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    have heven : Even (2 * k) := ⟨k, by omega⟩
    rw [abs_of_neg hxlt, heven.neg_pow]

theorem absSchattenNorm_even_pow_eq_trace {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (k : ℕ) (hk : 1 ≤ k) :
    absSchattenNorm (2 * (k : ℝ)) H ^ (2 * k) =
      Matrix.trace ((toFullBlockMat H) ^ (2 * k)) := by
  have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by norm_num
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hparam : (1 : ℝ) ≤ 2 * (k : ℝ) := by nlinarith
  calc
    absSchattenNorm (2 * (k : ℝ)) H ^ (2 * k)
        = absSchattenNorm (2 * (k : ℝ)) H ^ (2 * (k : ℝ)) := by
            rw [← Real.rpow_natCast, hcast]
    _ = ∑ i, |hH.eigenvalues i| ^ (2 * (k : ℝ)) :=
        absSchattenNorm_rpow_eq_sum hH hparam
    _ = ∑ i, hH.eigenvalues i ^ (2 * k : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← hcast, Real.rpow_natCast, abs_pow_even_two_mul]
    _ = Matrix.trace ((toFullBlockMat H) ^ (2 * k)) := by
        rw [← trace_cfc_eq_sum hH (fun x : ℝ => x ^ (2 * k : ℕ))]
        exact congrArg Matrix.trace
          (cfc_pow_id (R := ℝ) (a := toFullBlockMat H) (n := 2 * k) (ha := hH))

theorem blockTrace_nonneg {H : BlockMat d} (hH : (toFullBlockMat H).PosSemidef) :
    0 ≤ blockTrace H := by
  unfold blockTrace
  exact hH.trace_nonneg

private theorem finite_rpow_sum_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) {N : ℝ} (hN : 1 ≤ N) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i ^ N) ^ (1 / N) ≤ ∑ i ∈ s, f i := by
  classical
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNne : N ≠ 0 := hNpos.ne'
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, Real.zero_rpow (one_div_ne_zero hNne)]
  | insert a s has ih =>
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsumPow : 0 ≤ ∑ i ∈ s, f i ^ N :=
        Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hfs i hi) N
      have hroot : 0 ≤ (∑ i ∈ s, f i ^ N) ^ (1 / N) :=
        Real.rpow_nonneg hsumPow (1 / N)
      have hroot_pow :
          ((∑ i ∈ s, f i ^ N) ^ (1 / N)) ^ N = ∑ i ∈ s, f i ^ N := by
        rw [one_div]
        exact Real.rpow_inv_rpow hsumPow hNne
      rw [Finset.sum_insert has, Finset.sum_insert has]
      calc
        (f a ^ N + ∑ i ∈ s, f i ^ N) ^ (1 / N)
            = (f a ^ N + ((∑ i ∈ s, f i ^ N) ^ (1 / N)) ^ N) ^ (1 / N) := by
                rw [hroot_pow]
        _ ≤ f a + (∑ i ∈ s, f i ^ N) ^ (1 / N) :=
            Real.rpow_add_rpow_le_add hfa hroot hN
        _ ≤ f a + ∑ i ∈ s, f i := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left (ih hfs) (f a)

private theorem finite_abs_rpow_sum_le_abs_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) {N : ℝ} (hN : 1 ≤ N) :
    (∑ i ∈ s, |f i| ^ N) ^ N⁻¹ ≤ ∑ i ∈ s, |f i| := by
  rw [← one_div]
  exact finite_rpow_sum_le_sum s (fun i => |f i|) hN fun i _ => abs_nonneg (f i)

private theorem l2_opNorm_conjStarAlgAut {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℝ)) (A : Matrix n n ℝ) :
    ‖(Unitary.conjStarAlgAut ℝ _ U) A‖ = ‖A‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary
    (A := (U : Matrix n n ℝ) * A) (hU := Unitary.star_mem U.prop)]
  exact CStarRing.norm_mem_unitary_mul A U.prop

private theorem hermitian_l2_opNorm_eq_eigenvalue_norm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) :
    ‖toFullBlockMat H‖ = ‖hH.eigenvalues‖ := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [l2_opNorm_conjStarAlgAut]
  simp

private theorem abs_eigenvalue_le_l2_opNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (i : BlockCoord d) :
    |hH.eigenvalues i| ≤ ‖toFullBlockMat H‖ := by
  rw [hermitian_l2_opNorm_eq_eigenvalue_norm hH]
  simpa [Real.norm_eq_abs] using norm_le_pi_norm hH.eigenvalues i

private theorem abs_eigenvalue_le_absSchattenNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) (i : BlockCoord d) :
    |hH.eigenvalues i| ≤ absSchattenNorm N H := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNne : N ≠ 0 := (ne_of_lt hNpos).symm
  have hterm_nonneg : 0 ≤ |hH.eigenvalues i| ^ N :=
    Real.rpow_nonneg (abs_nonneg _) N
  have hterm_le_sum :
      |hH.eigenvalues i| ^ N ≤ ∑ j : BlockCoord d, |hH.eigenvalues j| ^ N :=
    Finset.single_le_sum (fun _ _ => Real.rpow_nonneg (abs_nonneg _) N) (Finset.mem_univ i)
  have hinv_nonneg : 0 ≤ 1 / N := by positivity
  calc
    |hH.eigenvalues i| = (|hH.eigenvalues i| ^ N) ^ (1 / N) := by
      rw [one_div, ← Real.rpow_mul (abs_nonneg (hH.eigenvalues i)) N N⁻¹,
        mul_inv_cancel₀ hNne, Real.rpow_one]
    _ ≤ (∑ j : BlockCoord d, |hH.eigenvalues j| ^ N) ^ (1 / N) :=
      Real.rpow_le_rpow hterm_nonneg hterm_le_sum hinv_nonneg
    _ = schattenNormEigen hH N := by
      unfold schattenNormEigen
      rw [one_div]
    _ = absSchattenNorm N H := (absSchattenNorm_eq_eigenvalues hH hN).symm

theorem absSchattenNorm_one_eq_blockTrace {H : BlockMat d}
    (hH : (toFullBlockMat H).PosSemidef) : absSchattenNorm 1 H = blockTrace H := by
  let hHerm := hH.isHermitian
  calc
    absSchattenNorm 1 H = schattenNormEigen hHerm 1 :=
      absSchattenNorm_eq_eigenvalues hHerm le_rfl
    _ = blockTrace H := by
      unfold schattenNormEigen blockTrace
      rw [inv_one, Real.rpow_one, hHerm.trace_eq_sum_eigenvalues]
      have hEigNonneg : 0 ≤ hHerm.eigenvalues :=
        hHerm.posSemidef_iff_eigenvalues_nonneg.mp hH
      apply Finset.sum_congr rfl
      intro i _hi
      simpa using (abs_of_nonneg (hEigNonneg i))

theorem absSchattenNorm_le_blockTrace {H : BlockMat d}
    (hH : (toFullBlockMat H).PosSemidef) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N H ≤ blockTrace H := by
  let hHerm := hH.isHermitian
  calc
    absSchattenNorm N H = schattenNormEigen hHerm N :=
      absSchattenNorm_eq_eigenvalues hHerm hN
    _ ≤ ∑ i : BlockCoord d, |hHerm.eigenvalues i| := by
      unfold schattenNormEigen
      exact finite_abs_rpow_sum_le_abs_sum Finset.univ hHerm.eigenvalues hN
    _ = blockTrace H := by
      unfold blockTrace
      rw [hHerm.trace_eq_sum_eigenvalues]
      have hEigNonneg : 0 ≤ hHerm.eigenvalues :=
        hHerm.posSemidef_iff_eigenvalues_nonneg.mp hH
      apply Finset.sum_congr rfl
      intro i _hi
      exact abs_of_nonneg (hEigNonneg i)

theorem blockOpNorm_le_absSchattenNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    blockOpNorm H ≤ absSchattenNorm N H := by
  unfold blockOpNorm
  rw [hermitian_l2_opNorm_eq_eigenvalue_norm hH]
  refine (pi_norm_le_iff_of_nonneg (absSchattenNorm_nonneg hH hN)).mpr ?_
  intro i
  simpa [Real.norm_eq_abs] using abs_eigenvalue_le_absSchattenNorm hH hN i

theorem blockTrace_le_dim_mul_blockOpNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).PosSemidef) :
    blockTrace H ≤ (2 * (d : ℝ)) * blockOpNorm H := by
  let hHerm := hH.isHermitian
  have hEigNonneg : 0 ≤ hHerm.eigenvalues :=
    hHerm.posSemidef_iff_eigenvalues_nonneg.mp hH
  calc
    blockTrace H = ∑ i : BlockCoord d, hHerm.eigenvalues i := by
      unfold blockTrace
      rw [hHerm.trace_eq_sum_eigenvalues]
      rfl
    _ ≤ ∑ _i : BlockCoord d, blockOpNorm H := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (le_abs_self (hHerm.eigenvalues i)).trans
        (by simpa [blockOpNorm] using abs_eigenvalue_le_l2_opNorm hHerm i)
    _ = (Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (2 * (d : ℝ)) * blockOpNorm H := by
      have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
        simp only [BlockCoord, Fintype.card_sum, Fintype.card_fin]
        rw [Nat.cast_add]
        ring
      rw [hcard]

end

end Homogenization.HighContrast.Analysis
