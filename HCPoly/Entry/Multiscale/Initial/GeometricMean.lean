import HCPoly.Entry.Multiscale.Initial.ScalarBounds

/-!
# Initialization: the matrix geometric mean and the square-root order toolkit

Operator-order support for the two entry-radius kernels of
`HCPoly/Entry/Multiscale/Initial/CanonicalMetric.lean`: monotonicity of the matrix square root,
Loewner congruence and inversion, and the matrix geometric mean `A #ᵐ B` with its
Riccati characterization, commutativity, monotonicity in both arguments and homogeneity
(`p.global.selection`).

These are helper facts of the initialization route, kept in the `GeoMean` namespace; they
carry no probability law and no annealed premise.
-/

open Homogenization.HighContrast (matSqrt matSqrt_eq matSqrt_spec)
namespace Homogenization.HighContrast.Multiscale

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

namespace GeoMean

/-! ## Public geometric-mean toolkit

These helpers support the entry-radius kernels in
HCPoly/Entry/Multiscale/Initial/CanonicalMetric.lean. -/


open Matrix

/-! ## Part 1. The matrix geometric mean -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! Ported square-root order toolkit. -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Small algebraic helpers ported from `HCPoly.Geometry.OperatorOrder` /
`HCPoly.Geometry.SqrtOrder`. -/

omit [Fintype ι] [DecidableEq ι] in
theorem conjTranspose_eq_transpose' (A : Matrix ι ι ℝ) : Aᴴ = Aᵀ :=
  Matrix.conjTranspose_eq_transpose_of_trivial A

omit [DecidableEq ι] in
/-- Congruence is monotone: conjugating both sides of a Loewner inequality by the same
matrix preserves it. -/
theorem conj_le_conj (C : Matrix ι ι ℝ) {A B : Matrix ι ι ℝ} (h : A ≤ B) :
    Cᴴ * A * C ≤ Cᴴ * B * C := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hconj := hPS.conjTranspose_mul_mul_same C
  rw [Matrix.le_iff]
  have hrw : Cᴴ * B * C - Cᴴ * A * C = Cᴴ * (B - A) * C := by noncomm_ring
  rw [hrw]
  exact hconj

omit [DecidableEq ι] in
/-- Congruence by a symmetric matrix preserves the Loewner order. -/
theorem conj_le_conj' {A B C : Matrix ι ι ℝ} (hC : Cᴴ = C) (h : A ≤ B) :
    C * A * C ≤ C * B * C := by
  have := conj_le_conj C h
  rwa [hC] at this

theorem matSqrtPosDef' {A : Matrix ι ι ℝ} (hA : A.PosDef) : (matSqrt A).PosDef := by
  rw [matSqrt_eq_cfc_sqrt hA.posSemidef]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (Matrix.isStrictlyPositive_iff_posDef.mpr hA).sqrt

theorem isUnit_det_of_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit

theorem norm_mul_self_of_symm {X : Matrix ι ι ℝ} (hX : Xᴴ = X) :
    ‖X * X‖ = ‖X‖ ^ 2 := by
  have h := CStarRing.norm_star_mul_self (x := X)
  rw [Matrix.star_eq_conjTranspose, hX] at h
  rw [h, sq]

theorem isHermitian_pow {X : Matrix ι ι ℝ} (hX : Xᴴ = X) (m : ℕ) :
    (X ^ m)ᴴ = X ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.conjTranspose_mul, hX, ih, ← pow_succ', pow_succ]

omit [DecidableEq ι] in
theorem inner_toLp (x y : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, dotProduct, RCLike.inner_apply, mul_comm]

omit [DecidableEq ι] in
theorem norm_toLp_sq' (x : ι → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]

theorem toEuclideanCLM_apply' (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (WithLp.toLp 2 x)
      = WithLp.toLp 2 (A *ᵥ x) := rfl

omit [DecidableEq ι] in
theorem dotProduct_mulVec_symm {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (x y : ι → ℝ) :
    x ⬝ᵥ A *ᵥ y = (A *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

theorem le_of_sq_le_sq' {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  have hsq := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hv] at hsq
  exact le_trans (le_abs_self u) hsq

theorem dotProduct_mulVec_le_norm_mul (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ ‖A‖ * (x ⬝ᵥ x) := by
  have hcs : x ⬝ᵥ A *ᵥ x ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ ι)‖ := by
    rw [← inner_toLp x (A *ᵥ x)]
    exact real_inner_le_norm _ _
  have hop : ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ ι)‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
    rw [← toEuclideanCLM_apply' A x, Matrix.cstar_norm_def]
    exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm _
  have hx : (0 : ℝ) ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := norm_nonneg _
  calc x ⬝ᵥ A *ᵥ x
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ *
          ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ ι)‖ := hcs
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ *
          (‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖) :=
        mul_le_mul_of_nonneg_left hop hx
    _ = ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 := by ring
    _ = ‖A‖ * (x ⬝ᵥ x) := by rw [norm_toLp_sq']

theorem norm_le_of_le_smul_one {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 ≤ t) (h : A ≤ t • (1 : Matrix ι ι ℝ)) : ‖A‖ ≤ t := by
  have hq : ∀ x : ι → ℝ, x ⬝ᵥ A *ᵥ x ≤ t * (x ⬝ᵥ x) := by
    intro x
    have hPS := Matrix.posSemidef_iff_dotProduct_mulVec.mp (Matrix.le_iff.mp h)
    have hx := hPS.2 x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul] at hx
    simp only [star_trivial, smul_eq_mul] at hx
    linarith only [hx]
  have hsq : ∀ x : ι → ℝ, x ⬝ᵥ (A * A) *ᵥ x ≤ t * (x ⬝ᵥ A *ᵥ x) := by
    intro x
    obtain ⟨hBpsd, hBB⟩ := matSqrt_spec hA
    set B : Matrix ι ι ℝ := matSqrt A with hBdef
    have hBsymm : Bᵀ = B := by
      rw [← conjTranspose_eq_transpose']; exact hBpsd.isHermitian
    have h1 : (B *ᵥ x) ⬝ᵥ A *ᵥ (B *ᵥ x) ≤ t * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) := hq (B *ᵥ x)
    have hLHS : (B *ᵥ x) ⬝ᵥ A *ᵥ (B *ᵥ x) = x ⬝ᵥ (A * A) *ᵥ x := by
      have hBAB : B * A * B = A * A := by rw [← hBB]; noncomm_ring
      rw [← dotProduct_mulVec_symm hBsymm x (A *ᵥ (B *ᵥ x)), Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hBAB]
    have hRHS : (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = x ⬝ᵥ A *ᵥ x := by
      rw [← dotProduct_mulVec_symm hBsymm x (B *ᵥ x), Matrix.mulVec_mulVec, hBB]
    rw [hLHS, hRHS] at h1
    exact h1
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ ht fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x : ι → ℝ, y = WithLp.toLp 2 x := ⟨WithLp.ofLp y, rfl⟩
  rw [toEuclideanCLM_apply']
  refine le_of_sq_le_sq' (mul_nonneg ht (norm_nonneg _)) ?_
  rw [norm_toLp_sq', mul_pow, norm_toLp_sq']
  have hAsymm : Aᵀ = A := by
    rw [← conjTranspose_eq_transpose']; exact hA.isHermitian
  have hexp : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A * A) *ᵥ x := by
    rw [← dotProduct_mulVec_symm hAsymm x (A *ᵥ x), Matrix.mulVec_mulVec]
  have h2 := hsq x
  have h3 := hq x
  have h4 : t * (x ⬝ᵥ A *ᵥ x) ≤ t * (t * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left h3 ht
  rw [hexp]
  calc x ⬝ᵥ (A * A) *ᵥ x ≤ t * (x ⬝ᵥ A *ᵥ x) := h2
    _ ≤ t * (t * (x ⬝ᵥ x)) := h4
    _ = t ^ 2 * (x ⬝ᵥ x) := by ring

theorem le_smul_one_of_norm_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {t : ℝ}
    (h : ‖A‖ ≤ t) : A ≤ t • (1 : Matrix ι ι ℝ) := by
  have hherm : (t • (1 : Matrix ι ι ℝ) - A).IsHermitian := by
    refine Matrix.IsHermitian.sub ?_ hA.isHermitian
    simp [Matrix.IsHermitian]
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_)
  have hbound := dotProduct_mulVec_le_norm_mul A x
  have hxx : (0 : ℝ) ≤ x ⬝ᵥ x := by
    rw [← norm_toLp_sq']; positivity
  have hstep : ‖A‖ * (x ⬝ᵥ x) ≤ t * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_right h hxx
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul]
  simp only [star_trivial, smul_eq_mul]
  linarith only [hbound, hstep]

theorem norm_le_one_of_le_one {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (h : X ≤ 1) : ‖X‖ ≤ 1 := by
  refine norm_le_of_le_smul_one hX zero_le_one ?_
  rwa [one_smul]

/-- **Operator monotonicity of the positive semidefinite square root.** -/
theorem sqrtMono' {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosDef) (h : A ≤ B) : matSqrt A ≤ matSqrt B := by
  set S : Matrix ι ι ℝ := matSqrt A with hSdef
  set T : Matrix ι ι ℝ := matSqrt B with hTdef
  have hSpsd : S.PosSemidef := (matSqrt_spec hA).1
  have hSS : S * S = A := (matSqrt_spec hA).2
  have hSsymm : Sᴴ = S := hSpsd.isHermitian
  have hT : T.PosDef := matSqrtPosDef' hB
  have hTT : T * T = B := (matSqrt_spec hB.posSemidef).2
  have hTsymm : Tᴴ = T := hT.isHermitian
  have hTdet : IsUnit T.det := isUnit_det_of_posDef hT
  have hTinvsymm : (T⁻¹)ᴴ = T⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hTsymm]
  have hTBT : T⁻¹ * B * T⁻¹ = 1 := by
    calc T⁻¹ * B * T⁻¹ = T⁻¹ * (T * T) * T⁻¹ := by rw [hTT]
      _ = (T⁻¹ * T) * (T * T⁻¹) := by noncomm_ring
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hTdet, Matrix.mul_nonsing_inv _ hTdet, Matrix.one_mul]
  set N : Matrix ι ι ℝ := S * T⁻¹ with hNdef
  have hNN : Nᴴ * N = T⁻¹ * A * T⁻¹ := by
    rw [hNdef, Matrix.conjTranspose_mul, hTinvsymm, hSsymm]
    calc T⁻¹ * S * (S * T⁻¹) = T⁻¹ * (S * S) * T⁻¹ := by noncomm_ring
      _ = T⁻¹ * A * T⁻¹ := by rw [hSS]
  have hNpsd : (Nᴴ * N).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self N
  have hNle : Nᴴ * N ≤ 1 := by
    have hc := conj_le_conj' hTinvsymm h
    rw [hTBT] at hc
    rwa [hNN]
  have hNnorm : ‖N‖ ≤ 1 := by
    have h1 : ‖Nᴴ * N‖ ≤ 1 := norm_le_one_of_le_one hNpsd hNle
    rw [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self (x := N)] at h1
    nlinarith only [h1, norm_nonneg N]
  set Q : Matrix ι ι ℝ := matSqrt T⁻¹ with hQdef
  have hQ : Q.PosDef := matSqrt_inv_posDef_full hT
  have hQsymm : Qᴴ = Q := hQ.isHermitian
  have hQQ : Q * Q = T⁻¹ := (matSqrt_spec hT.inv.posSemidef).2
  have hQdet : IsUnit Q.det := isUnit_det_of_posDef hQ
  set W : Matrix ι ι ℝ := Q * S * Q with hWdef
  have hWpsd : W.PosSemidef := by
    have hc := hSpsd.conjTranspose_mul_mul_same (B := Q)
    rwa [hQsymm] at hc
  have hWsymm : Wᴴ = W := hWpsd.isHermitian
  have hfact : ∀ m : ℕ, W ^ (m + 1) = Q * N ^ m * S * Q := by
    intro m
    induction m with
    | zero => simp [hWdef]
    | succ k ih =>
        have hstep : W ^ (k + 2) = (Q * N ^ k * S * Q) * W := by
          rw [pow_succ, ih]
        rw [hstep, hWdef]
        calc Q * N ^ k * S * Q * (Q * S * Q)
            = Q * N ^ k * S * (Q * Q) * S * Q := by noncomm_ring
          _ = Q * N ^ k * (S * T⁻¹) * S * Q := by rw [hQQ]; noncomm_ring
          _ = Q * N ^ (k + 1) * S * Q := by rw [← hNdef, pow_succ]; noncomm_ring
  set C₀ : ℝ := ‖Q‖ * ‖S‖ * ‖Q‖ with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  have hbound : ∀ m : ℕ, 1 ≤ m → ‖W ^ m‖ ≤ C₀ := by
    intro m hm
    match m, hm with
    | 1, _ =>
        rw [pow_one, hWdef]
        calc ‖Q * S * Q‖ ≤ ‖Q * S‖ * ‖Q‖ := norm_mul_le _ _
          _ ≤ (‖Q‖ * ‖S‖) * ‖Q‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Q)
    | (k + 2), _ =>
        have hNk : ‖N ^ (k + 1)‖ ≤ 1 := by
          have h1 : ‖N ^ (k + 1)‖ ≤ ‖N‖ ^ (k + 1) := norm_pow_le' N k.succ_pos
          have h2 : ‖N‖ ^ (k + 1) ≤ 1 ^ (k + 1) :=
            pow_le_pow_left₀ (norm_nonneg N) hNnorm (k + 1)
          rw [one_pow] at h2
          exact h1.trans h2
        rw [hfact (k + 1)]
        calc ‖Q * N ^ (k + 1) * S * Q‖
            ≤ ‖Q * N ^ (k + 1) * S‖ * ‖Q‖ := norm_mul_le _ _
          _ ≤ (‖Q * N ^ (k + 1)‖ * ‖S‖) * ‖Q‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Q)
          _ ≤ ((‖Q‖ * ‖N ^ (k + 1)‖) * ‖S‖) * ‖Q‖ := by
              have := norm_mul_le Q (N ^ (k + 1))
              have h3 : ‖Q * N ^ (k + 1)‖ * ‖S‖ ≤ (‖Q‖ * ‖N ^ (k + 1)‖) * ‖S‖ :=
                mul_le_mul_of_nonneg_right this (norm_nonneg S)
              exact mul_le_mul_of_nonneg_right h3 (norm_nonneg Q)
          _ ≤ ((‖Q‖ * 1) * ‖S‖) * ‖Q‖ := by
              have h4 : ‖Q‖ * ‖N ^ (k + 1)‖ ≤ ‖Q‖ * 1 :=
                mul_le_mul_of_nonneg_left hNk (norm_nonneg Q)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h4 (norm_nonneg S)) (norm_nonneg Q)
          _ = C₀ := by rw [hC₀def]; ring
  have hpow : ∀ k : ℕ, ‖W ^ 2 ^ k‖ = ‖W‖ ^ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have hsplit : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
        rw [hsplit, pow_add, norm_mul_self_of_symm (isHermitian_pow hWsymm (2 ^ j)), ih,
          ← pow_mul, mul_two]
  have hWnorm : ‖W‖ ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (R := ℝ) C₀ hcon
    have hmono : ‖W‖ ^ m ≤ ‖W‖ ^ 2 ^ m :=
      pow_le_pow_right₀ hcon.le (Nat.le_of_lt (Nat.lt_two_pow_self))
    have hle := hbound (2 ^ m) (Nat.one_le_two_pow)
    rw [hpow m] at hle
    linarith only [hm, hmono, hle]
  have hWle : W ≤ 1 := by
    have := le_smul_one_of_norm_le hWpsd hWnorm
    rwa [one_smul] at this
  have hQinvsymm : (Q⁻¹)ᴴ = Q⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hQsymm]
  have hcong := conj_le_conj' hQinvsymm hWle
  have hleft : Q⁻¹ * W * Q⁻¹ = S := by
    rw [hWdef]
    calc Q⁻¹ * (Q * S * Q) * Q⁻¹ = (Q⁻¹ * Q) * S * (Q * Q⁻¹) := by noncomm_ring
      _ = S := by
          rw [Matrix.nonsing_inv_mul _ hQdet, Matrix.mul_nonsing_inv _ hQdet,
            Matrix.one_mul, Matrix.mul_one]
  have hright : Q⁻¹ * 1 * Q⁻¹ = T := by
    rw [Matrix.mul_one, ← Matrix.mul_inv_rev, hQQ,
      Matrix.nonsing_inv_nonsing_inv _ hTdet]
  rwa [hleft, hright] at hcong


theorem detUnit {A : Matrix ι ι ℝ} (hA : A.PosDef) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit

theorem matSqrtHerm' {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (matSqrt A)ᴴ = matSqrt A := (matSqrt_spec hA).1.isHermitian.eq

theorem matSqrtInv' {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    matSqrt A⁻¹ = (matSqrt A)⁻¹ := by
  refine matSqrt_eq hA.inv.posSemidef (matSqrtPosDef' hA).inv.posSemidef ?_
  rw [← Matrix.mul_inv_rev, (matSqrt_spec hA.posSemidef).2]

omit [DecidableEq ι] in
theorem conjLe' {A B C : Matrix ι ι ℝ} (hC : Cᴴ = C) (h : A ≤ B) :
    C * A * C ≤ C * B * C := by
  have hBA : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hc := hBA.conjTranspose_mul_mul_same C
  rw [hC] at hc
  have heq : C * (B - A) * C = C * B * C - C * A * C := by noncomm_ring
  rw [heq] at hc
  exact Matrix.le_iff.mpr hc

theorem posDefConj' {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (B * A * B).PosDef := by
  have hBinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hB.isUnit
  have h := hA.conjTranspose_mul_mul_same (B := B) hBinj
  rwa [hB.isHermitian.eq] at h

theorem invAnti' {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hle : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have hD : (A⁻¹ - B⁻¹).IsHermitian := hA.inv.isHermitian.sub hB.inv.isHermitian
  have h₁ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  have h₂ := (Matrix.le_iff.mp hle).conjTranspose_mul_mul_same B⁻¹
  rw [hD.eq] at h₁
  rw [hB.inv.isHermitian.eq] at h₂
  apply Matrix.le_iff.mpr
  convert h₁.add h₂ using 1 <;> try rfl
  have hAiA := Matrix.nonsing_inv_mul A (detUnit hA)
  have hAAi := Matrix.mul_nonsing_inv A (detUnit hA)
  have hBiB := Matrix.nonsing_inv_mul B (detUnit hB)
  simp only [mul_sub, sub_mul, hAiA, hBiB, one_mul]
  rw [mul_assoc B⁻¹ A A⁻¹, hAAi, mul_one]
  abel

theorem smulInv' {A : Matrix ι ι ℝ} (hA : A.PosDef) {a : ℝ} (ha : a ≠ 0) :
    (a • A)⁻¹ = a⁻¹ • A⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha,
    Matrix.mul_nonsing_inv A (detUnit hA), one_smul]

/-- The matrix geometric mean `A # B = A^{1/2}(A^{-1/2} B A^{-1/2})^{1/2} A^{1/2}`. -/
def geoMean (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  matSqrt A * matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) * matSqrt A

theorem normPosDef' {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (matSqrt A⁻¹ * B * matSqrt A⁻¹).PosDef :=
  posDefConj' hB (matSqrtPosDef' hA.inv)

theorem geoMeanPosDef {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (geoMean A B).PosDef :=
  posDefConj' (matSqrtPosDef' (normPosDef' hA hB)) (matSqrtPosDef' hA)

theorem sqrtCancel {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    matSqrt A * matSqrt A⁻¹ = 1 ∧ matSqrt A⁻¹ * matSqrt A = 1 := by
  have hu : IsUnit (matSqrt A).det := detUnit (matSqrtPosDef' hA)
  rw [matSqrtInv' hA]
  exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu⟩

theorem riccatiOfRoots {P R S B : Matrix ι ι ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) (hSS : S * S = R * B * R) :
    P * S * P * (R * R) * (P * S * P) = B := by
  calc P * S * P * (R * R) * (P * S * P)
      = P * S * ((P * R) * (R * P)) * S * P := by noncomm_ring
    _ = P * (S * S) * P := by rw [hPR, hRP]; noncomm_ring
    _ = (P * R) * B * (R * P) := by rw [hSS]; noncomm_ring
    _ = B := by rw [hPR, hRP, Matrix.one_mul, Matrix.mul_one]

theorem geoMean_riccati {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    geoMean A B * A⁻¹ * geoMean A B = B := by
  obtain ⟨hPR, hRP⟩ := sqrtCancel hA
  have hSS := (matSqrt_spec (normPosDef' hA hB).posSemidef).2
  have key := riccatiOfRoots hPR hRP hSS
  rw [(matSqrt_spec hA.inv.posSemidef).2] at key
  exact key

theorem eq_geoMean_of_riccati {A B X : Matrix ι ι ℝ} (hA : A.PosDef)
    (hX : X.PosDef) (h : X * A⁻¹ * X = B) : X = geoMean A B := by
  have hRR : matSqrt A⁻¹ * matSqrt A⁻¹ = A⁻¹ := (matSqrt_spec hA.inv.posSemidef).2
  have hY : (matSqrt A⁻¹ * X * matSqrt A⁻¹).PosDef := posDefConj' hX (matSqrtPosDef' hA.inv)
  have hYY : (matSqrt A⁻¹ * X * matSqrt A⁻¹) * (matSqrt A⁻¹ * X * matSqrt A⁻¹)
      = matSqrt A⁻¹ * B * matSqrt A⁻¹ := by
    calc (matSqrt A⁻¹ * X * matSqrt A⁻¹) * (matSqrt A⁻¹ * X * matSqrt A⁻¹)
        = matSqrt A⁻¹ * X * (matSqrt A⁻¹ * matSqrt A⁻¹) * X * matSqrt A⁻¹ := by noncomm_ring
      _ = matSqrt A⁻¹ * (X * A⁻¹ * X) * matSqrt A⁻¹ := by rw [hRR]; noncomm_ring
      _ = matSqrt A⁻¹ * B * matSqrt A⁻¹ := by rw [h]
  have hM : (matSqrt A⁻¹ * B * matSqrt A⁻¹).PosSemidef := by
    rw [← hYY]
    have hq := Matrix.posSemidef_conjTranspose_mul_self (matSqrt A⁻¹ * X * matSqrt A⁻¹)
    rwa [hY.isHermitian.eq] at hq
  have hYsqrt : matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) = matSqrt A⁻¹ * X * matSqrt A⁻¹ :=
    matSqrt_eq hM hY.posSemidef hYY
  obtain ⟨hPR, hRP⟩ := sqrtCancel hA
  calc X = (matSqrt A * matSqrt A⁻¹) * X * (matSqrt A⁻¹ * matSqrt A) := by
        rw [hPR, hRP, Matrix.one_mul, Matrix.mul_one]
    _ = matSqrt A * (matSqrt A⁻¹ * X * matSqrt A⁻¹) * matSqrt A := by noncomm_ring
    _ = matSqrt A * matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) * matSqrt A := by rw [hYsqrt]
    _ = geoMean A B := rfl

theorem invRiccati {A B X : Matrix ι ι ℝ} (h : X * A⁻¹ * X = B) :
    X⁻¹ * (A⁻¹)⁻¹ * X⁻¹ = B⁻¹ := by
  rw [← h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

theorem eq_geoMean_comm_of_riccati {A B X : Matrix ι ι ℝ} (hA : A.PosDef)
    (hB : B.PosDef) (hX : X.PosDef) (hric : X * A⁻¹ * X = B) : X = geoMean B A := by
  have hinv : X⁻¹ * A * X⁻¹ = B⁻¹ := by
    have h := invRiccati hric
    rwa [Matrix.nonsing_inv_nonsing_inv _ (detUnit hA)] at h
  refine eq_geoMean_of_riccati hB hX ?_
  have hstep : X * (X⁻¹ * A * X⁻¹) * X = A := by
    calc X * (X⁻¹ * A * X⁻¹) * X = (X * X⁻¹) * A * (X⁻¹ * X) := by noncomm_ring
      _ = A := by
          rw [Matrix.mul_nonsing_inv _ (detUnit hX), Matrix.nonsing_inv_mul _ (detUnit hX),
            Matrix.one_mul, Matrix.mul_one]
  rw [← hstep, hinv]

theorem geoMean_comm {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    geoMean A B = geoMean B A :=
  eq_geoMean_comm_of_riccati hA hB (geoMeanPosDef hA hB) (geoMean_riccati hA hB)

theorem geoMean_mono_right {A B₀ B₁ : Matrix ι ι ℝ} (hA : A.PosDef)
    (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef) (h : B₀ ≤ B₁) :
    geoMean A B₀ ≤ geoMean A B₁ := by
  have hRsymm : (matSqrt A⁻¹)ᴴ = matSqrt A⁻¹ := matSqrtHerm' hA.inv.posSemidef
  have hPsymm : (matSqrt A)ᴴ = matSqrt A := matSqrtHerm' hA.posSemidef
  have hnorm : matSqrt A⁻¹ * B₀ * matSqrt A⁻¹ ≤ matSqrt A⁻¹ * B₁ * matSqrt A⁻¹ :=
    conjLe' hRsymm h
  have hroot := sqrtMono' (normPosDef' hA hB₀).posSemidef (normPosDef' hA hB₁) hnorm
  exact conjLe' hPsymm hroot

theorem geoMean_mono {A₀ A₁ B₀ B₁ : Matrix ι ι ℝ} (hA₀ : A₀.PosDef)
    (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    (hA : A₀ ≤ A₁) (hB : B₀ ≤ B₁) :
    geoMean A₀ B₀ ≤ geoMean A₁ B₁ := by
  have h1 : geoMean A₀ B₀ ≤ geoMean A₀ B₁ := geoMean_mono_right hA₀ hB₀ hB₁ hB
  have h2 : geoMean B₁ A₀ ≤ geoMean B₁ A₁ := geoMean_mono_right hB₁ hA₀ hA₁ hA
  rw [← geoMean_comm hA₀ hB₁, geoMean_comm hB₁ hA₁] at h2
  exact h1.trans h2

theorem geoMean_self {A : Matrix ι ι ℝ} (hA : A.PosDef) : geoMean A A = A := by
  refine (eq_geoMean_of_riccati hA hA ?_).symm
  rw [Matrix.mul_nonsing_inv _ (detUnit hA), Matrix.one_mul]

theorem geoMean_smul {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    geoMean (a • A) (b • B) = Real.sqrt (a * b) • geoMean A B := by
  have hab : 0 < a * b := mul_pos ha hb
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
  have hss : Real.sqrt (a * b) * Real.sqrt (a * b) = a * b := Real.mul_self_sqrt hab.le
  have hX : (Real.sqrt (a * b) • geoMean A B).PosDef := (geoMeanPosDef hA hB).smul hs
  refine (eq_geoMean_of_riccati (hA.smul ha) hX ?_).symm
  rw [smulInv' hA ha.ne']
  have hscal : Real.sqrt (a * b) • geoMean A B * (a⁻¹ • A⁻¹) *
      (Real.sqrt (a * b) • geoMean A B) =
      (Real.sqrt (a * b) * a⁻¹ * Real.sqrt (a * b)) • (geoMean A B * A⁻¹ * geoMean A B) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
  rw [hscal, geoMean_riccati hA hB]
  congr 1
  have hre : Real.sqrt (a * b) * a⁻¹ * Real.sqrt (a * b)
      = Real.sqrt (a * b) * Real.sqrt (a * b) * a⁻¹ := by ring
  rw [hre, hss]
  field_simp

end GeoMean

end

end Homogenization.HighContrast.Multiscale
