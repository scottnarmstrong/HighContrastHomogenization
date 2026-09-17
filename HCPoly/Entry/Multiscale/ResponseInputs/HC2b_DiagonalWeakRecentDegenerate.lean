import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# The degenerate metric branches of the diagonal weak-norm primal bound

The binders of `diagonalWeakNorm_primal_le`
(`HC2b_DiagonalWeakRecent.lean`) give an ARBITRARY `F : BlockMat d`, so neither
`(explicitCanonicalMetric F).PosDef` nor `(toFullBlockMat (respM0 F)).PosDef` is available, while
the pointwise cell-defect estimates were stated with both.  The degenerate branches are
settled WITHOUT a statement change, by showing that they are harmless.
This file does the metric half of that, from the bottom up: it identifies exactly which junk
value `matSqrt` (`HCPoly/Setup/BlockAlgebra.lean`) returns in each degeneration of
`respM0 F = diag(m, m⁻¹)`, `m = explicitCanonicalMetric F` (`HCPoly/Entry/Setup/CanonicalMetric.lean`).

The structural fact that makes the classification finite is that `explicitCanonicalMetric F` is the
Mathlib inverse of a matrix, so it is EITHER a unit OR literally `0` — there is no
"singular but nonzero" metric.  Hence exactly three branches:

* `m` a unit and `toFullBlockMat (respM0 F)` positive definite — the nondegenerate branch, the
  one the pointwise cell-defect estimate already covers;
* `m = 0` — then `toFullBlockMat (respM0 F) = 0` and `blockSqrt (respM0 F) = 0`, so the
  left-hand side of the diagonal weak-norm bound is identically `0`;
* `m` a unit but `toFullBlockMat (respM0 F)` NOT positive definite (equivalently: not positive
  semidefinite, since a unit PSD matrix is PosDef) — then `matSqrt` falls through on BOTH
  `respM0 F` and its inverse, so `blockSqrt (respM0 F)` is the identity and
  `normalizedBlock E (respM0 F)` is `E` itself.  The metric simply disappears from both
  sides, and the cell step becomes its own `M_0 = I` instance.

These degenerations are self-consistent, and the lemmas below establish that fact.

With an explicit hypothesis `hm : m.PosDef` on the metric, these branches cannot arise; they are
exactly the cost of the binder-free carrier map `respM0 F`.
-/

open Homogenization.HighContrast (matSqrt normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-! ## The two junk values of `matSqrt` -/

/-- `matSqrt M` is the junk value `1` as soon as `M` is not positive semidefinite: a
positive semidefinite `B` with `B * B = M` would exhibit `M = Bᴴ * B` as positive semidefinite. -/
theorem matSqrt_eq_one_of_not_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : ¬ M.PosSemidef) : matSqrt M = 1 := by
  have hno : ¬ ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = M := by
    rintro ⟨B, hB, hBB⟩
    refine hM ?_
    have hBH : Bᴴ * B = M := by rw [hB.isHermitian.eq]; exact hBB
    rw [← hBH]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  simp only [matSqrt, dif_neg hno]

/-- `matSqrt 0 = 0`. -/
theorem matSqrt_zero {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (0 : Matrix n n ℝ) = 0 := by
  rw [matSqrt_eq_cfc_sqrt Matrix.PosSemidef.zero]
  exact CFC.sqrt_zero

/-- `matSqrt 1 = 1`, the nondegenerate companion of the previous result. -/
theorem matSqrt_one {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (1 : Matrix n n ℝ) = 1 := by
  rw [matSqrt_eq_cfc_sqrt Matrix.PosSemidef.one]
  exact CFC.sqrt_one

variable {d : ℕ}

/-! ## The dichotomy of the canonical metric -/

/-- `explicitCanonicalMetric F` is a Mathlib matrix inverse, so it is either invertible or
literally `0`: there is no "singular but nonzero" canonical metric.  This is what makes the
degenerate classification finite. -/
theorem explicitCanonicalMetric_eq_zero_of_not_isUnit {F : BlockMat d}
    (h : ¬ IsUnit (explicitCanonicalMetric F).det) : explicitCanonicalMetric F = 0 := by
  rw [explicitCanonicalMetric] at h ⊢
  refine Matrix.nonsing_inv_apply_not_isUnit _ ?_
  intro hu
  exact h (Matrix.isUnit_nonsing_inv_det _ hu)

/-- When the canonical metric degenerates, the entire metric block does. -/
theorem toFullBlockMat_respM0_eq_zero {F : BlockMat d} (h : explicitCanonicalMetric F = 0) :
    toFullBlockMat (respM0 F) = 0 := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, respM0, h, Matrix.inv_zero]

/-- `blockSqrt` of a vanishing metric block vanishes. -/
theorem blockSqrt_respM0_eq_zero {F : BlockMat d} (h : explicitCanonicalMetric F = 0) :
    blockSqrt (respM0 F) = ofFullBlockMat 0 := by
  rw [blockSqrt, toFullBlockMat_respM0_eq_zero h, matSqrt_zero]

/-- Consequently every `M_0^{1/2}`-transported vector vanishes, so the left-hand side of the
diagonal weak-norm bound is identically `0` in this branch. -/
theorem blockMatVecMul_blockSqrt_respM0_eq_zero {F : BlockMat d} (h : explicitCanonicalMetric F = 0)
    (Y : BlockVec d) : blockMatVecMul (blockSqrt (respM0 F)) Y = 0 := by
  rw [blockSqrt_respM0_eq_zero h]
  ext i <;> simp [blockMatVecMul, matVecMul, ofFullBlockMat]

/-! ## The indefinite branch: the metric disappears from both sides -/

/-- If the metric block is not positive semidefinite, `blockSqrt (respM0 F)` is the junk
identity, so `M_0^{1/2}` acts trivially on the left-hand side of the diagonal weak-norm bound. -/
theorem toFullBlockMat_blockSqrt_respM0_eq_one {F : BlockMat d}
    (h : ¬ (toFullBlockMat (respM0 F)).PosSemidef) :
    toFullBlockMat (blockSqrt (respM0 F)) = 1 := by
  rw [blockSqrt, toFullBlockMat_ofFullBlockMat, matSqrt_eq_one_of_not_posSemidef h]

/-- In the same branch the INVERSE metric block is not positive semidefinite either, as
soon as the metric is a unit, so `normalizedBlock E (respM0 F)` is `E` itself: the printed
constant `K_0` degenerates to `‖E‖` and nothing is lost. -/
theorem toFullBlockMat_normalizedBlock_respM0_eq_self {F : BlockMat d} (E : BlockMat d)
    (hu : IsUnit (toFullBlockMat (respM0 F)).det)
    (h : ¬ (toFullBlockMat (respM0 F)).PosSemidef) :
    toFullBlockMat (normalizedBlock E (respM0 F)) = toFullBlockMat E := by
  have hinv : ¬ ((toFullBlockMat (respM0 F))⁻¹).PosSemidef := by
    intro hpsd
    refine h ?_
    have : (toFullBlockMat (respM0 F))⁻¹⁻¹ = toFullBlockMat (respM0 F) :=
      Matrix.nonsing_inv_nonsing_inv _ hu
    rw [← this]
    exact hpsd.inv
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, matSqrt_eq_one_of_not_posSemidef hinv,
    one_mul, mul_one]

/-! ## Invertibility and the metric restriction on the unit branch -/

/-- The explicit left inverse of the flattened metric block on the unit branch.  This is
the computational core of the metric inverse lemma (`h6a_toFullBlockMat_respM0_inv`,
`HC2b_DiagonalWeakRecent.lean`), isolated here because it needs only `IsUnit` of the metric
determinant, not positive definiteness. -/
theorem toFullBlockMat_respM0_left_inv {F : BlockMat d}
    (hu : IsUnit (explicitCanonicalMetric F).det) :
    toFullBlockMat (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ : BlockMat d) *
        toFullBlockMat (respM0 F) = 1 := by
  have hmm : (explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F = 1 := Matrix.nonsing_inv_mul _ hu
  have hmm' : explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have hij : ∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j
          = ((explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F) i j := (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j) +
          (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) = _ from rfl]
      simp [hij, hmm, Matrix.one_apply]
    | inr j =>
      simp [toFullBlockMat, respM0]
  | inr i =>
    cases b with
    | inl j =>
      simp [toFullBlockMat, respM0]
    | inr j =>
      have hij : ∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j
          = (explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹) i j := (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) +
          (∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j) = _ from rfl]
      simp [hij, hmm', Matrix.one_apply]

/-- Hence on the unit branch the flattened metric block is invertible, with NO
positivity assumption whatsoever. -/
theorem isUnit_det_toFullBlockMat_respM0 {F : BlockMat d}
    (hu : IsUnit (explicitCanonicalMetric F).det) : IsUnit (toFullBlockMat (respM0 F)).det :=
  Matrix.isUnit_det_of_left_inverse (toFullBlockMat_respM0_left_inv hu)

/-- The canonical metric inherits positive semidefiniteness from the flattened metric
block: restrict the quadratic form to the first slot. -/
theorem posSemidef_explicitCanonicalMetric_of_respM0 {F : BlockMat d}
    (h : (toFullBlockMat (respM0 F)).PosSemidef) : (explicitCanonicalMetric F).PosSemidef := by
  have hherm : (explicitCanonicalMetric F).IsHermitian := by
    have hH := h.1
    ext i j
    have := congrFun (congrFun hH (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.conjTranspose_apply, toFullBlockMat, respM0] using this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm ?_
  intro v
  have hq := h.dotProduct_mulVec_nonneg (toFullBlockVec ((v, 0) : BlockVec d))
  have hblock : blockMatVecMul (respM0 F) ((v, 0) : BlockVec d)
      = (matVecMul (explicitCanonicalMetric F) v, 0) := by
    ext i <;> simp [blockMatVecMul, respM0, matVecMul]
  have hrw : star (toFullBlockVec ((v, 0) : BlockVec d)) ⬝ᵥ
        toFullBlockMat (respM0 F) *ᵥ toFullBlockVec ((v, 0) : BlockVec d)
      = v ⬝ᵥ explicitCanonicalMetric F *ᵥ v := by
    rw [star_trivial, ← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec, hblock]
    simp [blockVecDot, vecDot, dotProduct, Matrix.mulVec, matVecMul]
  rwa [hrw] at hq

/-! ## The `Ehat` degeneration

The OTHER degenerate side is the one where the congruenced annealed block
`Ehat_t^- = respEhatMinus P jStar F t` is singular; the statements recorded here do not close it. -/

/-! ## The load collapse, one sub-case of the `Ehat` degeneration

If `respEhatMinus` is singular then `respLsqMinus = 0` forces the loads to vanish.  That is TRUE
in the sub-case where the degeneration sits in the lower-right block of the annealed mean — but
only there; the remaining sub-case resists. -/

end

end Homogenization.HighContrast.Multiscale
