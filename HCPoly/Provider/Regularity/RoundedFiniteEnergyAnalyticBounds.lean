/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.FiniteLipschitzCoreBase
import HCPoly.Provider.Regularity.RoundedHarmonicComparisonSpecialization

/-!
# Analytic bounds for the rounded finite energy recurrence

This file derives the Poincare and coarse-Caccioppoli inputs used in the
printed finite energy-row recurrence directly from the genuinely rounded
comparison matrix and its fixed near-unity ellipticity window.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory Set Book.Ch03
open scoped BigOperators ENNReal Matrix MatrixOrder

noncomputable section

open FiniteLipschitzCoreInternal

namespace RoundedFiniteEnergyInternal

private theorem skewPart_eq_zero_of_isSymm
    {d : ℕ} {A : Mat d} (hA : A.IsSymm) :
    skewPart A = 0 := by
  ext i j
  have hij : A j i = A i j := (Matrix.IsSymm.ext_iff.mp hA) i j
  change (A i j - A j i) / 2 = 0
  rw [hij]
  ring

private theorem blockMatVecMul_constantBlockMatrix_of_isSymm
    {d : ℕ} {A : Mat d} (hA : A.IsSymm) (P : BlockVec d) :
    blockMatVecMul (Book.Ch02.constantBlockMatrix A) P =
      (matVecMul A P.1, matVecMul A⁻¹ P.2) := by
  rcases P with ⟨p, r⟩
  have hsymm : symmPart A = A := symmPart_eq_of_isSymm hA
  have hskew : skewPart A = 0 := skewPart_eq_zero_of_isSymm hA
  apply Prod.ext
  · simp [Book.Ch02.constantBlockMatrix, blockMatVecMul, hsymm, hskew,
      matTranspose]
    ext i
    simp [matVecMul]
  · simp [Book.Ch02.constantBlockMatrix, blockMatVecMul, hsymm, hskew,
      matTranspose]
    ext i
    simp [matVecMul]

private theorem vecDot_matVecMul_le_of_matrix_le
    {d : ℕ} {A B : Mat d} (h : A ≤ B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hdiff.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  change x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x
  simp only [star_trivial] at hx
  linarith only [hx]

private theorem vecNormSq_single_one {d : ℕ} (i : Fin d) :
    vecNormSq (Pi.single i 1 : Vec d) = 1 := by
  rw [vecNormSq, vecDot]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hji hji
    simp [Pi.single_eq_of_ne hji]
  · simp

private theorem roundedReference_coordinate_quadratic_bounds
    {d : ℕ} [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    (99 / 100 : ℝ) ≤
        vecDot (Pi.single i 1 : Vec d)
          (matVecMul (roundedReferenceMatrix abar hS) (Pi.single i 1)) ∧
      vecDot (Pi.single i 1 : Vec d)
          (matVecMul (roundedReferenceMatrix abar hS) (Pi.single i 1)) ≤
        (101 / 100 : ℝ) := by
  let e : Vec d := Pi.single i 1
  let A : Mat d := roundedReferenceMatrix abar hS
  obtain ⟨hlower, hupper⟩ :=
    roundedSymmetricReferenceCoefficient_order_bounds abar hS (0 : Vec d)
  have hlow := vecDot_matVecMul_le_of_matrix_le hlower e
  have hupp := vecDot_matVecMul_le_of_matrix_le hupper e
  have he : vecNormSq e = 1 := by
    simpa only [e] using vecNormSq_single_one i
  have hscalar (c : ℝ) :
      vecDot e (matVecMul (c • (1 : Mat d)) e) = c * vecNormSq e := by
    have hone : matVecMul (1 : Mat d) e = e := by
      funext j
      simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [smul_matVecMul, hone, vecDot_smul_right]
    rfl
  change (99 / 100 : ℝ) ≤ vecDot e (matVecMul A e) ∧
    vecDot e (matVecMul A e) ≤ (101 / 100 : ℝ)
  constructor
  · simpa only [hscalar, he, mul_one, A, e] using! hlow
  · simpa only [hscalar, he, mul_one, A, e] using! hupp

private theorem doubledResponseJ_le_normalizedBlockResponseMax_of_quadratic_one
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (P : BlockVec d)
    (hquad : blockVecDot P
      (blockMatVecMul
        (Book.Ch02.constantBlockMatrix (roundedReferenceMatrix abar hS)) P) = 1) :
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (a.coeffOn Q) P
        (blockMatVecMul
          (Book.Ch02.constantBlockMatrix (roundedReferenceMatrix abar hS)) P) ≤
      Book.Ch02.normalizedBlockResponseMax Q a
        (roundedReferenceMatrix abar hS) := by
  have hmem :=
    Book.Ch02.normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
      Q a (isEllipticMatrix_roundedReferenceMatrix abar hS) P hquad
  unfold Book.Ch02.normalizedBlockResponseMax
  exact le_csSup
    (Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := a) (Q := Q) (R := Q) (k := Q.scale)
      (roundedReferenceMatrix abar hS)
      (by simp [descendantsAtScale_self])) hmem

private theorem coarseB_diagonal_le_roundedResponse
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i ≤
      2 * (101 / 100 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := by
  let U := Book.Ch02.cubeDomain Q
  let aQ := a.coeffOn Q
  let A : Mat d := roundedReferenceMatrix abar hS
  let e : Vec d := Pi.single i 1
  let r : ℝ := vecDot e (matVecMul A e)
  let c : ℝ := (Real.sqrt r)⁻¹
  let P₀ : BlockVec d := (e, 0)
  let P : BlockVec d := c • P₀
  let B := Book.Ch02.coarseBlockMatrix U aQ
  let BStar := Book.Ch02.coarseStarredBlockMatrixInv U aQ
  let M := Book.Ch02.normalizedBlockResponseMax Q a A
  have hAsymm : A.IsSymm :=
    isSymm_of_isHermitian (roundedReferenceMatrix_posDef abar hS).isHermitian
  obtain ⟨hrlow, hrupp⟩ :=
    roundedReference_coordinate_quadratic_bounds abar hS i
  have hrpos : 0 < r := by dsimp only [r, e, A]; linarith only [hrlow]
  have hCP₀ : blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀ =
      (matVecMul A e, 0) := by
    rw [blockMatVecMul_constantBlockMatrix_of_isSymm hAsymm]
    simp only [P₀, matVecMul_zero]
  have hquad₀ : blockVecDot P₀
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀) = r := by
    rw [hCP₀]
    simp only [P₀, blockVecDot, vecDot_zero_left, add_zero, r, e]
  have hquad : blockVecDot P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) = 1 := by
    rw [show P = c • P₀ from rfl, blockMatVecMul_smul,
      blockVecDot_smul_left, blockVecDot_smul_right, hquad₀]
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hJ : Book.Ch02.doubledResponseJ U aQ P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) ≤ M := by
    simpa only [U, aQ, A, M] using
      doubledResponseJ_le_normalizedBlockResponseMax_of_quadratic_one
        Q a abar hS P (by simpa only [A] using hquad)
  let Qv := blockMatVecMul (Book.Ch02.constantBlockMatrix A) P
  have hQquad_nonneg : 0 ≤ blockVecDot Qv (blockMatVecMul BStar Qv) := by
    by_cases hQv : Qv = 0
    · rw [hQv]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · exact ((Book.Ch02.blockCoarseMatrixTheory U aQ).starred_inverse_posDef
        Qv hQv).le
  have hpair : blockVecDot P Qv = 1 := by
    simpa only [Qv] using hquad
  have hsplit :=
    (Book.Ch02.blockCoarseMatrixTheory U aQ).doubled_response_splitting P Qv
  have hscaled : blockVecDot P (blockMatVecMul B P) ≤ 2 * (M + 1) := by
    rw [hsplit, hpair] at hJ
    nlinarith only [hJ, hQquad_nonneg]
  have hx : blockVecDot P (blockMatVecMul B P) =
      c * c * Book.Ch02.bCoarse U aQ i i := by
    have hbase : blockVecDot P₀ (blockMatVecMul B P₀) =
        Book.Ch02.bCoarse U aQ i i := by
      dsimp only [P₀, B]
      simp only [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left,
        add_zero]
      dsimp only [e]
      rw [vecDot_single_left, matVecMul_single]
      rfl
    rw [show P = c • P₀ from rfl, blockMatVecMul_smul,
      blockVecDot_smul_left, blockVecDot_smul_right, hbase]
    ring
  rw [hx] at hscaled
  have hc : r * (c * c) = 1 := by
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hMnonneg : 0 ≤ M := by
    exact Book.Ch02.normalizedBlockResponseMax_nonneg Q a A
  calc
    Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i =
        r * (c * c * Book.Ch02.bCoarse U aQ i i) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ r * (2 * (M + 1)) := mul_le_mul_of_nonneg_left hscaled hrpos.le
    _ ≤ 2 * (101 / 100 : ℝ) * (M + 1) := by
      have hrupp' : r ≤ (101 / 100 : ℝ) := by
        simpa only [r, e, A] using hrupp
      nlinarith only [hrupp', hMnonneg]
    _ = 2 * (101 / 100 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := rfl

private theorem roundedReference_inverse_coordinate_quadratic_bounds
    {d : ℕ} [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    (101 / 100 : ℝ)⁻¹ ≤
        vecDot (Pi.single i 1 : Vec d)
          (matVecMul (roundedReferenceMatrix abar hS)⁻¹ (Pi.single i 1)) ∧
      vecDot (Pi.single i 1 : Vec d)
          (matVecMul (roundedReferenceMatrix abar hS)⁻¹ (Pi.single i 1)) ≤
        (99 / 100 : ℝ)⁻¹ := by
  let e : Vec d := Pi.single i 1
  let A : Mat d := roundedReferenceMatrix abar hS
  have hAell := isEllipticMatrix_roundedReferenceMatrix abar hS
  have hAsymm : A.IsSymm :=
    isSymm_of_isHermitian (roundedReferenceMatrix_posDef abar hS).isHermitian
  have he : vecNormSq e = 1 := by
    simpa only [e] using vecNormSq_single_one i
  have hlower := hAell.2.2.2 e
  have hupper := symmPart_inv_upperBound_of_isEllipticMatrix hAell e
  have hsymm : symmPart A = A := symmPart_eq_of_isSymm hAsymm
  change (101 / 100 : ℝ)⁻¹ ≤ vecDot e (matVecMul A⁻¹ e) ∧
    vecDot e (matVecMul A⁻¹ e) ≤ (99 / 100 : ℝ)⁻¹
  constructor
  · simpa only [he, mul_one, A, e] using hlower
  · simpa only [hsymm, he, mul_one, A, e] using hupper

private theorem coarseSigmaStarInv_diagonal_le_roundedResponse
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (i : Fin d) :
    Book.Ch02.sigmaStarInvCoarse
        (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i ≤
      2 * (100 / 99 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := by
  let U := Book.Ch02.cubeDomain Q
  let aQ := a.coeffOn Q
  let A : Mat d := roundedReferenceMatrix abar hS
  let e : Vec d := Pi.single i 1
  let r : ℝ := vecDot e (matVecMul A⁻¹ e)
  let c : ℝ := (Real.sqrt r)⁻¹
  let P₀ : BlockVec d := (matVecMul A⁻¹ e, 0)
  let P : BlockVec d := c • P₀
  let Q₀ : BlockVec d := (e, 0)
  let B := Book.Ch02.coarseBlockMatrix U aQ
  let BStar := Book.Ch02.coarseStarredBlockMatrixInv U aQ
  let M := Book.Ch02.normalizedBlockResponseMax Q a A
  have hAell := isEllipticMatrix_roundedReferenceMatrix abar hS
  have hAsymm : A.IsSymm :=
    isSymm_of_isHermitian (roundedReferenceMatrix_posDef abar hS).isHermitian
  have hAdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hAell
  obtain ⟨hrlow, hrupp⟩ :=
    roundedReference_inverse_coordinate_quadratic_bounds abar hS i
  have hrpos : 0 < r := by dsimp only [r, e, A]; linarith only [hrlow]
  have hAAinvE : matVecMul A (matVecMul A⁻¹ e) = e := by
    rw [matVecMul_mul, Matrix.mul_nonsing_inv A hAdet, matVecMul_one]
  have hCP₀ : blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀ = Q₀ := by
    rw [blockMatVecMul_constantBlockMatrix_of_isSymm hAsymm]
    simp only [P₀, Q₀, matVecMul_zero, hAAinvE]
  have hquad₀ : blockVecDot P₀
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P₀) = r := by
    rw [hCP₀]
    simp only [P₀, Q₀, blockVecDot, vecDot_zero_left, add_zero,
      vecDot_comm (matVecMul A⁻¹ e) e, r]
  have hquad : blockVecDot P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) = 1 := by
    rw [show P = c • P₀ from rfl, blockMatVecMul_smul,
      blockVecDot_smul_left, blockVecDot_smul_right, hquad₀]
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hJ : Book.Ch02.doubledResponseJ U aQ P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix A) P) ≤ M := by
    simpa only [U, aQ, A, M] using
      doubledResponseJ_le_normalizedBlockResponseMax_of_quadratic_one
        Q a abar hS P (by simpa only [A] using hquad)
  let Qv := blockMatVecMul (Book.Ch02.constantBlockMatrix A) P
  have hPquad_nonneg : 0 ≤ blockVecDot P (blockMatVecMul B P) := by
    by_cases hPzero : P = 0
    · rw [hPzero]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · exact ((Book.Ch02.blockCoarseMatrixTheory U aQ).block_matrix_posDef
        P hPzero).le
  have hpair : blockVecDot P Qv = 1 := by
    simpa only [Qv] using hquad
  have hsplit :=
    (Book.Ch02.blockCoarseMatrixTheory U aQ).doubled_response_splitting P Qv
  have hscaled : blockVecDot Qv (blockMatVecMul BStar Qv) ≤ 2 * (M + 1) := by
    rw [hsplit, hpair] at hJ
    nlinarith only [hJ, hPquad_nonneg]
  have hQv : Qv = c • Q₀ := by
    dsimp only [Qv, P]
    rw [blockMatVecMul_smul, hCP₀]
  have hx : blockVecDot Qv (blockMatVecMul BStar Qv) =
      c * c * Book.Ch02.sigmaStarInvCoarse U aQ i i := by
    have hbase : blockVecDot Q₀ (blockMatVecMul BStar Q₀) =
        Book.Ch02.sigmaStarInvCoarse U aQ i i := by
      dsimp only [Q₀, BStar]
      simp only [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left,
        add_zero]
      dsimp only [e]
      rw [vecDot_single_left, matVecMul_single]
      rfl
    rw [hQv, blockMatVecMul_smul, blockVecDot_smul_left,
      blockVecDot_smul_right, hbase]
    ring
  rw [hx] at hscaled
  have hc : r * (c * c) = 1 := by
    dsimp only [c]
    field_simp [Real.sqrt_pos.2 hrpos]
    rw [Real.sq_sqrt hrpos.le]
  have hMnonneg : 0 ≤ M := by
    exact Book.Ch02.normalizedBlockResponseMax_nonneg Q a A
  calc
    Book.Ch02.sigmaStarInvCoarse
          (Book.Ch02.cubeDomain Q) (a.coeffOn Q) i i =
        r * (c * c * Book.Ch02.sigmaStarInvCoarse U aQ i i) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ r * (2 * (M + 1)) := mul_le_mul_of_nonneg_left hscaled hrpos.le
    _ ≤ 2 * (100 / 99 : ℝ) * (M + 1) := by
      have hrupp' : r ≤ (100 / 99 : ℝ) := calc
        r ≤ (99 / 100 : ℝ)⁻¹ := by
          simpa only [r, e, A] using hrupp
        _ = (100 / 99 : ℝ) := by norm_num
      nlinarith only [hrupp', hMnonneg]
    _ = 2 * (100 / 99 : ℝ) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := rfl

/-- The one-cube upper coarse ellipticity norm is controlled directly by the
rounded-reference response. -/
theorem coarseBMatrixNorm_le_roundedReferenceResponse
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    Book.Ch02.coarseBMatrixNorm Q a ≤
      (d : ℝ) * (2 * (101 / 100 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := by
  let K : ℝ := 2 * (101 / 100 : ℝ) *
    (Book.Ch02.normalizedBlockResponseMax Q a
      (roundedReferenceMatrix abar hS) + 1)
  have htrace : Matrix.trace
      (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) ≤
        ∑ _i : Fin d, K := by
    exact Finset.sum_le_sum fun i _hi ↦ by
      simpa only [K] using! coarseB_diagonal_le_roundedResponse Q a abar hS i
  calc
    Book.Ch02.coarseBMatrixNorm Q a ≤ Matrix.trace
        (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) := by
      exact Book.Ch02.matrixNorm_le_trace_of_posSemidef _
        (Book.Ch02.bCoarse_posSemidef _ _)
    _ ≤ ∑ _i : Fin d, K := htrace
    _ = (d : ℝ) * K := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (d : ℝ) * (2 * (101 / 100 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := by
      dsimp only [K]
      ring

/-- The one-cube lower coarse ellipticity inverse norm is controlled directly
by the rounded-reference response. -/
theorem coarseSigmaStarInvMatrixNorm_le_roundedReferenceResponse
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    Book.Ch02.coarseSigmaStarInvMatrixNorm Q a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := by
  let K : ℝ := 2 * (100 / 99 : ℝ) *
    (Book.Ch02.normalizedBlockResponseMax Q a
      (roundedReferenceMatrix abar hS) + 1)
  have htrace : Matrix.trace
      (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) ≤
        ∑ _i : Fin d, K := by
    exact Finset.sum_le_sum fun i _hi ↦ by
      simpa only [K, Matrix.diag_apply] using
        coarseSigmaStarInv_diagonal_le_roundedResponse Q a abar hS i
  calc
    Book.Ch02.coarseSigmaStarInvMatrixNorm Q a ≤ Matrix.trace
        (Book.Ch02.sigmaStarInvCoarse
          (Book.Ch02.cubeDomain Q) (a.coeffOn Q)) := by
      exact Book.Ch02.matrixNorm_le_trace_of_posSemidef _
        (Book.Ch02.sigmaStarInvCoarse_posDef _ _).posSemidef
    _ ≤ ∑ _i : Fin d, K := htrace
    _ = (d : ℝ) * K := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := by
      dsimp only [K]
      ring

private theorem coarseBMatrixNorm_le_commonRoundedResponse
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    Book.Ch02.coarseBMatrixNorm Q a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.normalizedBlockResponseMax Q a
          (roundedReferenceMatrix abar hS) + 1) := by
  let M := Book.Ch02.normalizedBlockResponseMax Q a
    (roundedReferenceMatrix abar hS)
  have hraw := coarseBMatrixNorm_le_roundedReferenceResponse Q a abar hS
  have hM : 0 ≤ M :=
    Book.Ch02.normalizedBlockResponseMax_nonneg Q a
      (roundedReferenceMatrix abar hS)
  have hcoeff :
      (d : ℝ) * (2 * (101 / 100 : ℝ)) ≤
        (d : ℝ) * (2 * (100 / 99 : ℝ)) := by
    have hd : (0 : ℝ) ≤ d := by positivity
    nlinarith only [hd]
  exact hraw.trans
    (mul_le_mul_of_nonneg_right hcoeff (by linarith only [hM]))

private theorem maxDescendantBMatrixNormAtScale_le_commonRoundedResponse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : Book.Ch02.TriadicCoeffFamily d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    Book.Ch02.maxDescendantBMatrixNormAtScale Q k a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
          (roundedReferenceMatrix abar hS) + 1) := by
  let C : ℝ := (d : ℝ) * (2 * (100 / 99 : ℝ)) *
    (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
      (roundedReferenceMatrix abar hS) + 1)
  have hD : (descendantsAtScale Q k).Nonempty :=
    descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Book.Ch02.coarseBMatrixNorm R a ≤ C := by
    intro R hR
    have hRone := coarseBMatrixNorm_le_commonRoundedResponse R a abar hS
    have hMle :
        Book.Ch02.normalizedBlockResponseMax R a
            (roundedReferenceMatrix abar hS) ≤
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
            (roundedReferenceMatrix abar hS) :=
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a (roundedReferenceMatrix abar hS) hR
    have hcoef : 0 ≤ (d : ℝ) * (2 * (100 / 99 : ℝ)) := by positivity
    dsimp only [C]
    exact hRone.trans
      (mul_le_mul_of_nonneg_left (by linarith only [hMle]) hcoef)
  simpa only [Book.Ch02.maxDescendantBMatrixNormAtScale] using
    Book.Ch02.finsetSupReal_le (descendantsAtScale Q k) hD hpoint

private theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_commonRoundedResponse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : Book.Ch02.TriadicCoeffFamily d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      (d : ℝ) * (2 * (100 / 99 : ℝ)) *
        (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
          (roundedReferenceMatrix abar hS) + 1) := by
  let C : ℝ := (d : ℝ) * (2 * (100 / 99 : ℝ)) *
    (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
      (roundedReferenceMatrix abar hS) + 1)
  have hD : (descendantsAtScale Q k).Nonempty :=
    descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Book.Ch02.coarseSigmaStarInvMatrixNorm R a ≤ C := by
    intro R hR
    have hRone :=
      coarseSigmaStarInvMatrixNorm_le_roundedReferenceResponse R a abar hS
    have hMle :
        Book.Ch02.normalizedBlockResponseMax R a
            (roundedReferenceMatrix abar hS) ≤
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a
            (roundedReferenceMatrix abar hS) :=
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a (roundedReferenceMatrix abar hS) hR
    have hcoef : 0 ≤ (d : ℝ) * (2 * (100 / 99 : ℝ)) := by positivity
    dsimp only [C]
    exact hRone.trans
      (mul_le_mul_of_nonneg_left (by linarith only [hMle]) hcoef)
  simpa only [Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale] using
    Book.Ch02.finsetSupReal_le (descendantsAtScale Q k) hD hpoint

end RoundedFiniteEnergyInternal

end

end HighContrast
end Homogenization
