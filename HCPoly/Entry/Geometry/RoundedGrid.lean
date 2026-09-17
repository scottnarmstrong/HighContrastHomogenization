import HCPoly.Entry.Geometry.PositiveSqrt
import HCPoly.Entry.Geometry.RoundedGridDef
import HCPoly.Entry.Geometry.SourceWhitney
import HCPoly.Setup.Geometry

/-!
# The rounded grid `𝒬(𝔪)` and `e.rounded.grid.bounds`

Near `e.rounded.grid.bounds`.  Fix `j_* ∈ ℕ` with `3^{j_*} ≥ 2d`.  For every positive
matrix `𝔪`,

  `(𝒬(𝔪))_{ab} := 3^{-j_*} ⌈ 3^{j_*} |𝔪⁻¹|^{1/2} (𝔪^{1/2})_{ab} ⌉`.

Here `|·|` is the Euclidean operator norm (Mathlib's `‖·‖` under `Matrix.Norms.L2Operator`)
and `𝔪^{1/2}` is `CFC.sqrt 𝔪`.  The print asserts: `𝒬(𝔪)` is symmetric; the rounding error has
operator norm at most `d 3^{-j_*} ≤ 1/2`; the unrounded matrix `|𝔪⁻¹|^{1/2} 𝔪^{1/2}` has smallest
eigenvalue `1` and largest eigenvalue `(|𝔪| |𝔪⁻¹|)^{1/2}`; hence (`e.rounded.grid.bounds`)

  `q ≥ ½ Id`,  `|q⁻¹| ≤ 2`,  `|q| ≤ 2 (|𝔪| |𝔪⁻¹|)^{1/2}`  for `q = 𝒬(𝔪)`;

and `3^j q ℤ^d ⊆ ℤ^d` for `j ≥ j_*`.

The definition `explicitRoundedGrid` itself lives in the definition-only leaf `HCPoly.Entry.Geometry.RoundedGridDef`
(imported here), separately from the proofs below.
`j_*` is a parameter of the definition (the entries depend on it) and the standing constraint
`3^{j_*} ≥ 2d` is a hypothesis `hj` on the theorems that use it; symmetry and the entrywise
rounding bound do not need it.  Each of the three bounds is given in the vector form used by
`l.source.whitney` and in Mathlib's operator-norm (or Loewner-order) form.  The bridge to node 1
is `inverseNormLE_roundedGrid`, and `source_whitney_roundedGrid` is the printed lemma with
`q = 𝒬(𝔪)`.
-/

open Homogenization.HighContrast (adaptedCellTranslate standardCell)
namespace Homogenization.HighContrast.Geometry

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

/-! ## Definitions -/

/-- The unrounded matrix `|𝔪⁻¹|^{1/2} 𝔪^{1/2}`. -/
noncomputable def unroundedGrid (m : Mat d) : Mat d :=
  Real.sqrt ‖m⁻¹‖ • CFC.sqrt m

variable {jStar : ℕ} {m : Mat d}

theorem unroundedGrid_apply (m : Mat d) (a b : Fin d) :
    unroundedGrid m a b = Real.sqrt ‖m⁻¹‖ * CFC.sqrt m a b := rfl

theorem explicitRoundedGrid_apply (jStar : ℕ) (m : Mat d) (a b : Fin d) :
    explicitRoundedGrid jStar m a b
      = ((3 : ℝ) ^ jStar)⁻¹ * (⌈(3 : ℝ) ^ jStar * unroundedGrid m a b⌉ : ℤ) := by
  simp only [explicitRoundedGrid, of_apply, unroundedGrid_apply, mul_assoc]
  rw [_root_.zpow_neg, zpow_natCast]

/-! ## Symmetry -/

theorem explicitRoundedGrid_transpose (hm : Matrix.PosDef m) :
    (explicitRoundedGrid jStar m)ᵀ = explicitRoundedGrid jStar m := by
  ext a b
  simp only [transpose_apply, explicitRoundedGrid, of_apply, sqrt_apply_comm hm a b]

/-! ## The rounding error -/

/-- Each entry of the rounding error `⌈x⌉ - x` scaled by `3^{-j_*}` has absolute value at most
`3^{-j_*}`. -/
theorem abs_roundedGrid_sub_unroundedGrid_le (jStar : ℕ) (m : Mat d) (a b : Fin d) :
    |explicitRoundedGrid jStar m a b - unroundedGrid m a b| ≤ ((3 : ℝ) ^ jStar)⁻¹ := by
  rw [explicitRoundedGrid_apply]
  set p : ℝ := (3 : ℝ) ^ jStar with hp
  set x : ℝ := p * unroundedGrid m a b with hx
  have hp0 : 0 < p := by positivity
  have key : p⁻¹ * (⌈x⌉ : ℝ) - unroundedGrid m a b = p⁻¹ * ((⌈x⌉ : ℝ) - x) := by
    rw [mul_sub, hx, ← mul_assoc, inv_mul_cancel₀ hp0.ne', one_mul]
  rw [key, abs_mul, abs_of_pos (inv_pos.mpr hp0)]
  have h1 := Int.le_ceil x
  have h2 := Int.ceil_lt_add_one x
  have h3 : |(⌈x⌉ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc p⁻¹ * |(⌈x⌉ : ℝ) - x| ≤ p⁻¹ * 1 := by gcongr
    _ = p⁻¹ := mul_one _

/-- The rounding error has operator norm at most `d 3^{-j_*}`, in vector form. -/
theorem vecNormSq_roundingError_mulVec_le (jStar : ℕ) (m : Mat d) (v : Vec d) :
    vecNormSq ((explicitRoundedGrid jStar m - unroundedGrid m) *ᵥ v)
      ≤ ((d : ℝ) * ((3 : ℝ) ^ jStar)⁻¹) ^ 2 * vecNormSq v := by
  set ε : ℝ := ((3 : ℝ) ^ jStar)⁻¹ with hε
  set E : Mat d := explicitRoundedGrid jStar m - unroundedGrid m with hE
  have hε0 : 0 ≤ ε := by positivity
  have hEab : ∀ a b, |E a b| ≤ ε := fun a b => by
    rw [hE, Matrix.sub_apply]
    exact abs_roundedGrid_sub_unroundedGrid_le jStar m a b
  have hs : (∑ b, |v b|) ^ 2 ≤ (d : ℝ) * vecNormSq v := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => |v b|) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sq_abs] at h
    rw [vecNormSq_eq_sum_sq, mul_comm]
    exact h
  have hrow : ∀ a, |(E *ᵥ v) a| ≤ ε * ∑ b, |v b| := by
    intro a
    simp only [mulVec, dotProduct]
    calc |∑ b, E a b * v b| ≤ ∑ b, |E a b * v b| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b, |E a b| * |v b| := by simp only [abs_mul]
      _ ≤ ∑ b, ε * |v b| :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hEab a b) (abs_nonneg _)
      _ = ε * ∑ b, |v b| := by rw [Finset.mul_sum]
  have hsum : ∑ a, (E *ᵥ v) a ^ 2 ≤ ∑ _a : Fin d, (ε * ∑ b, |v b|) ^ 2 :=
    Finset.sum_le_sum fun a _ => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hrow a) 2
  rw [vecNormSq_eq_sum_sq]
  calc ∑ a, (E *ᵥ v) a ^ 2 ≤ ∑ _a : Fin d, (ε * ∑ b, |v b|) ^ 2 := hsum
    _ = (d : ℝ) * (ε ^ 2 * (∑ b, |v b|) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow]
    _ ≤ (d : ℝ) * (ε ^ 2 * ((d : ℝ) * vecNormSq v)) := by gcongr
    _ = ((d : ℝ) * ε) ^ 2 * vecNormSq v := by ring

/-- The rounding error has operator norm at most `d 3^{-j_*}`. -/
theorem opNorm_roundingError_le (jStar : ℕ) (m : Mat d) :
    ‖explicitRoundedGrid jStar m - unroundedGrid m‖ ≤ (d : ℝ) * ((3 : ℝ) ^ jStar)⁻¹ :=
  opNorm_le_of_vecNormSq_mulVec_le (by positivity) (vecNormSq_roundingError_mulVec_le jStar m)

/-- The standing `3^{j_*} ≥ 2d` gives `d 3^{-j_*} ≤ 1/2`. -/
theorem mul_inv_pow_le_half (hj : 2 * d ≤ 3 ^ jStar) :
    (d : ℝ) * ((3 : ℝ) ^ jStar)⁻¹ ≤ 1 / 2 := by
  have hp : (0 : ℝ) < (3 : ℝ) ^ jStar := by positivity
  have h : (2 * d : ℝ) ≤ (3 : ℝ) ^ jStar := by exact_mod_cast hj
  rw [← div_eq_mul_inv, div_le_iff₀ hp]
  linarith

/-- The rounding error has operator norm at most `1/2`, in vector form. -/
theorem vecNormSq_roundingError_mulVec_le_half (m : Mat d) (hj : 2 * d ≤ 3 ^ jStar)
    (v : Vec d) :
    vecNormSq ((explicitRoundedGrid jStar m - unroundedGrid m) *ᵥ v) ≤ (1 / 2) ^ 2 * vecNormSq v :=
  (vecNormSq_roundingError_mulVec_le jStar m v).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (mul_inv_pow_le_half hj) 2) (vecNormSq_nonneg v))

theorem abs_dotProduct_roundingError_le (m : Mat d) (hj : 2 * d ≤ 3 ^ jStar) (v : Vec d) :
    |v ⬝ᵥ ((explicitRoundedGrid jStar m - unroundedGrid m) *ᵥ v)| ≤ 1 / 2 * vecNormSq v :=
  abs_dotProduct_mulVec_le_of_vecNormSq_le (by norm_num)
    (vecNormSq_roundingError_mulVec_le_half m hj) v

/-! ## The unrounded matrix -/

theorem dotProduct_unroundedGrid (m : Mat d) (v : Vec d) :
    v ⬝ᵥ (unroundedGrid m *ᵥ v) = Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (CFC.sqrt m *ᵥ v)) := by
  rw [unroundedGrid, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem dotProduct_roundedGrid_eq (jStar : ℕ) (m : Mat d) (v : Vec d) :
    v ⬝ᵥ (explicitRoundedGrid jStar m *ᵥ v)
      = v ⬝ᵥ (unroundedGrid m *ᵥ v)
        + v ⬝ᵥ ((explicitRoundedGrid jStar m - unroundedGrid m) *ᵥ v) := by
  have h : unroundedGrid m + (explicitRoundedGrid jStar m - unroundedGrid m) = explicitRoundedGrid jStar m := by
    abel
  rw [← dotProduct_add, ← add_mulVec, h]

/-- The smallest eigenvalue of the unrounded matrix is at least one: `|v|² ≤ ⟨v, U v⟩`. -/
theorem vecNormSq_le_dotProduct_unroundedGrid (hm : Matrix.PosDef m) (v : Vec d) :
    vecNormSq v ≤ v ⬝ᵥ (unroundedGrid m *ᵥ v) := by
  rw [dotProduct_unroundedGrid]
  exact vecNormSq_le_sqrt_opNorm_inv_mul_dotProduct_sqrt hm v

/-- The largest eigenvalue of the unrounded matrix is at most `(|𝔪| |𝔪⁻¹|)^{1/2}`:
`⟨v, U v⟩ ≤ (‖𝔪‖ ‖𝔪⁻¹‖)^{1/2} |v|²`. -/
theorem dotProduct_unroundedGrid_le (hm : Matrix.PosDef m) (v : Vec d) :
    v ⬝ᵥ (unroundedGrid m *ᵥ v) ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) * vecNormSq v := by
  rw [dotProduct_unroundedGrid, Real.sqrt_mul (norm_nonneg m)]
  have h := dotProduct_sqrt_le hm v
  calc Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (CFC.sqrt m *ᵥ v))
      ≤ Real.sqrt ‖m⁻¹‖ * (Real.sqrt ‖m‖ * vecNormSq v) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = Real.sqrt ‖m‖ * Real.sqrt ‖m⁻¹‖ * vecNormSq v := by ring

/-! ## `e.rounded.grid.bounds`, first bound: `q ≥ ½ Id` -/

theorem half_vecNormSq_le_dotProduct_roundedGrid (hj : 2 * d ≤ 3 ^ jStar)
    (hm : Matrix.PosDef m) (v : Vec d) :
    1 / 2 * vecNormSq v ≤ v ⬝ᵥ (explicitRoundedGrid jStar m *ᵥ v) := by
  rw [dotProduct_roundedGrid_eq]
  have h1 := vecNormSq_le_dotProduct_unroundedGrid hm v
  have h2 := (abs_le.mp (abs_dotProduct_roundingError_le m hj v)).1
  linarith

theorem dotProduct_roundedGrid_nonneg (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m)
    (v : Vec d) : 0 ≤ v ⬝ᵥ (explicitRoundedGrid jStar m *ᵥ v) :=
  (mul_nonneg (by norm_num) (vecNormSq_nonneg v)).trans
    (half_vecNormSq_le_dotProduct_roundedGrid hj hm v)

/-! ## Second bound: `|q⁻¹| ≤ 2`, and the bridge to `l.source.whitney` -/

/-- **The bridge to node 1**: `q = 𝒬(𝔪)` satisfies `|v|² ≤ 4 |q v|²`, i.e. `|q⁻¹| ≤ 2`. -/
theorem inverseNormLE_roundedGrid (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m) :
    InverseNormLE (explicitRoundedGrid jStar m) 2 := by
  intro v
  have h := vecNormSq_le_vecNormSq_mulVec_of_le_dotProduct (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (half_vecNormSq_le_dotProduct_roundedGrid hj hm) v
  rw [matVecMul_eq_mulVec]
  have e1 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  have e2 : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [e1] at h
  rw [e2]
  linarith

theorem isUnit_roundedGrid (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m) :
    IsUnit (explicitRoundedGrid jStar m) :=
  (inverseNormLE_roundedGrid hj hm).isUnit

/-- `|q⁻¹| ≤ 2` in vector form: `|q⁻¹ w|² ≤ 2² |w|²`. -/
theorem vecNormSq_roundedGrid_inv_mulVec_le (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m)
    (w : Vec d) : vecNormSq ((explicitRoundedGrid jStar m)⁻¹ *ᵥ w) ≤ 2 ^ 2 * vecNormSq w := by
  have hq := inverseNormLE_roundedGrid hj hm
  have hdet : IsUnit (explicitRoundedGrid jStar m).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hq.isUnit
  have h := hq ((explicitRoundedGrid jStar m)⁻¹ *ᵥ w)
  rwa [matVecMul_eq_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec] at h

/-- `|q⁻¹| ≤ 2` for the Euclidean operator norm. -/
theorem opNorm_roundedGrid_inv_le (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m) :
    ‖(explicitRoundedGrid jStar m)⁻¹‖ ≤ 2 :=
  opNorm_le_of_vecNormSq_mulVec_le (by norm_num) (vecNormSq_roundedGrid_inv_mulVec_le hj hm)

/-! ## Third bound: `|q| ≤ 2 (|𝔪| |𝔪⁻¹|)^{1/2}` -/

/-- `|𝔪| |𝔪⁻¹| ≥ 1` as soon as there is a nonzero vector. -/
theorem one_le_opNorm_mul_opNorm_inv (hm : Matrix.PosDef m) {v : Vec d} (hv : v ≠ 0) :
    1 ≤ ‖m‖ * ‖m⁻¹‖ := by
  have hdet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp hm.isUnit
  have h1 : vecNormSq v ≤ ‖m⁻¹‖ ^ 2 * vecNormSq (m *ᵥ v) := by
    have h := vecNormSq_mulVec_le_opNorm m⁻¹ (m *ᵥ v)
    rwa [mulVec_mulVec, Matrix.nonsing_inv_mul m hdet, one_mulVec] at h
  have h2 := vecNormSq_mulVec_le_opNorm m v
  have hv0 : 0 < vecNormSq v := by
    rcases (vecNormSq_nonneg v).lt_or_eq with h | h
    · exact h
    · exact absurd (vecNormSq_eq_zero_iff.mp h.symm) hv
  have h3 : 1 * vecNormSq v ≤ (‖m‖ * ‖m⁻¹‖) ^ 2 * vecNormSq v := by
    calc 1 * vecNormSq v = vecNormSq v := one_mul _
      _ ≤ ‖m⁻¹‖ ^ 2 * vecNormSq (m *ᵥ v) := h1
      _ ≤ ‖m⁻¹‖ ^ 2 * (‖m‖ ^ 2 * vecNormSq v) := by gcongr
      _ = (‖m‖ * ‖m⁻¹‖) ^ 2 * vecNormSq v := by ring
  have h4 : 1 ≤ (‖m‖ * ‖m⁻¹‖) ^ 2 := le_of_mul_le_mul_right h3 hv0
  have hK : 0 ≤ ‖m‖ * ‖m⁻¹‖ := by positivity
  exact (pow_le_pow_iff_left₀ zero_le_one hK two_ne_zero).mp (by rw [one_pow]; exact h4)

theorem dotProduct_roundedGrid_le (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m) (v : Vec d) :
    v ⬝ᵥ (explicitRoundedGrid jStar m *ᵥ v) ≤ 2 * Real.sqrt (‖m‖ * ‖m⁻¹‖) * vecNormSq v := by
  by_cases hv : v = 0
  · subst hv
    simp [vecNormSq, vecDot]
  · rw [dotProduct_roundedGrid_eq]
    have h1 := dotProduct_unroundedGrid_le hm v
    have h2 := (abs_le.mp (abs_dotProduct_roundingError_le m hj v)).2
    have h3 : 1 ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) := by
      rw [Real.le_sqrt zero_le_one (by positivity), one_pow]
      exact one_le_opNorm_mul_opNorm_inv hm hv
    have hv0 := vecNormSq_nonneg v
    have h4 : 1 / 2 * vecNormSq v ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) * vecNormSq v :=
      mul_le_mul_of_nonneg_right (by linarith) hv0
    linarith

/-- `|q| ≤ 2 (|𝔪| |𝔪⁻¹|)^{1/2}` in vector form. -/
theorem vecNormSq_roundedGrid_mulVec_le (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m)
    (v : Vec d) :
    vecNormSq (explicitRoundedGrid jStar m *ᵥ v)
      ≤ (2 * Real.sqrt (‖m‖ * ‖m⁻¹‖)) ^ 2 * vecNormSq v :=
  vecNormSq_mulVec_le_of_dotProduct_le (explicitRoundedGrid_transpose hm)
    (dotProduct_roundedGrid_nonneg hj hm) (by positivity) (dotProduct_roundedGrid_le hj hm) v

/-- `|q| ≤ 2 (|𝔪| |𝔪⁻¹|)^{1/2}` for the Euclidean operator norm. -/
theorem opNorm_roundedGrid_le (hj : 2 * d ≤ 3 ^ jStar) (hm : Matrix.PosDef m) :
    ‖explicitRoundedGrid jStar m‖ ≤ 2 * Real.sqrt (‖m‖ * ‖m⁻¹‖) :=
  opNorm_le_of_vecNormSq_mulVec_le (by positivity) (vecNormSq_roundedGrid_mulVec_le hj hm)

/-! ## Integrality: `3^j 𝒬(𝔪) ℤ^d ⊆ ℤ^d` for `j ≥ j_*` -/

/-- `3^j 𝒬(𝔪)` maps integer vectors to integer vectors whenever `j ≥ j_*`. -/
theorem explicitRoundedGrid_mulVec_intCast (jStar : ℕ) (m : Mat d) {j : ℤ} (hj : (jStar : ℤ) ≤ j)
    (w : Fin d → ℤ) :
    ∃ w' : Fin d → ℤ,
      (3 : ℝ) ^ j • (explicitRoundedGrid jStar m *ᵥ fun i => (w i : ℝ)) = fun i => (w' i : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (jStar : ℤ) + n :=
    ⟨(j - jStar).toNat, by rw [Int.toNat_of_nonneg (by linarith)]; ring⟩
  refine ⟨fun a => ∑ b, 3 ^ n * ⌈(3 : ℝ) ^ jStar * Real.sqrt ‖m⁻¹‖ * CFC.sqrt m a b⌉ * w b, ?_⟩
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, explicitRoundedGrid, of_apply,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast, _root_.zpow_neg,
    zpow_natCast]
  have h3 : (3 : ℝ) ^ jStar ≠ 0 := by positivity
  field_simp

/-! ## `l.source.whitney` at `q = 𝒬(𝔪)` -/

/-- **`l.source.whitney`, source-shaped.**  Let `𝔪 > 0`, `q = 𝒬(𝔪)`, `W = y + ⋄_j^q`.  The
maximal standard aligned cubes contained in `W` with generations at most `j` are pairwise
disjoint subsets of `W` covering `W` up to a null set, each generation `r ≤ j` has finitely
many of them, and `Σ_{z ∈ 𝒵_r(W)} |□_r| / |W| ≤ 12 d^{3/2} 3^{r-j}`. -/
theorem source_whitney_roundedGrid [NeZero d] (hj : 2 * d ≤ 3 ^ jStar)
    (hm : Matrix.PosDef m) (j : ℤ) (y : Vec d) :
    (∀ p ∈ maximalCellPairs (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) j,
        standardCell d p.1 p.2 ⊆ adaptedCellTranslate (explicitRoundedGrid jStar m) j y) ∧
      (maximalCellPairs (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) j).PairwiseDisjoint
        (fun p => standardCell d p.1 p.2) ∧
      MeasureTheory.volume (adaptedCellTranslate (explicitRoundedGrid jStar m) j y \
        ⋃ p ∈ maximalCellPairs (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) j,
          standardCell d p.1 p.2) = 0 ∧
      ∀ r ≤ j,
        ∃ hfin : (maximalCellIndices (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) j r).Finite,
          ∑ w ∈ hfin.toFinset,
              (MeasureTheory.volume (standardCell d r w)).toReal /
                (MeasureTheory.volume (adaptedCellTranslate (explicitRoundedGrid jStar m) j y)).toReal ≤
            12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (r - j) :=
  source_whitney (inverseNormLE_roundedGrid hj hm) j y

end Homogenization.HighContrast.Geometry
