/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.OperatorOrder
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Bochner integrals of matrices, and matrix Jensen

The averaging step of the annealed primal-adjoint order needs three things about the
expectation of a random symmetric matrix: that it is computed entrywise, that it
respects the Loewner order, and that it obeys the operator Jensen inequality for
the inverse.

The order statements are the generic Bochner ones, but they are unavailable off
the shelf: the Loewner order on `Matrix n n ℝ` is a scoped partial order and
Mathlib does not record that it is closed.  The first section supplies exactly
that, from the description of positive semidefiniteness as a symmetry condition
together with one nonnegativity condition per test vector — each of them closed,
because the matrix entries and the quadratic forms are continuous linear
functionals on a finite-dimensional space.

Matrix Jensen is the reference text's argument, unchanged: for positive definite
`Y` the doubled matrix `(Y I; I Y⁻¹)` is positive semidefinite, its Schur
complement in the lower right corner being zero; averaging the doubling of a
random `X` gives `(E X, I; I, E (X⁻¹))`, and reading the Schur complement of that
average in the upper left corner returns `(E X)⁻¹ ≤ E (X⁻¹)`.
-/

namespace Homogenization
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix
open MeasureTheory

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Loewner order is closed -/

/-- The quadratic form at a fixed vector, read as a linear functional of the
matrix. -/
private def quadForm (x : n → ℝ) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun A := star x ⬝ᵥ A *ᵥ x
  map_add' A B := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by simp [Matrix.smul_mulVec, dotProduct_smul]

/-- The quadratic form at a fixed vector is continuous, the matrices forming a
finite-dimensional normed space. -/
private def quadFormCLM (x : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (quadForm x)

omit [DecidableEq n] in
private theorem quadFormCLM_apply (x : n → ℝ) (A : Matrix n n ℝ) :
    quadFormCLM x A = star x ⬝ᵥ A *ᵥ x := rfl

/-- A single matrix entry, as a continuous linear functional. -/
private def entryCLM (i j : n) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)

omit [DecidableEq n] in
/-- **The positive semidefinite cone is closed.**  Symmetry is an intersection of
equalities between entries, and positivity is an intersection of inequalities
between continuous quadratic forms. -/
theorem isClosed_setOf_nonneg : IsClosed {A : Matrix n n ℝ | (0 : Matrix n n ℝ) ≤ A} := by
  have hset : {A : Matrix n n ℝ | (0 : Matrix n n ℝ) ≤ A} =
      (⋂ i : n, ⋂ j : n, {A : Matrix n n ℝ | A j i = A i j}) ∩
        ⋂ x : n → ℝ, {A : Matrix n n ℝ | 0 ≤ quadFormCLM x A} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, quadFormCLM_apply,
      Matrix.nonneg_iff_posSemidef, Matrix.posSemidef_iff_dotProduct_mulVec,
      Matrix.IsHermitian, ← Matrix.ext_iff, Matrix.conjTranspose_apply, star_trivial]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun x => ?_)
  · exact isClosed_eq (entryCLM j i).continuous (entryCLM i j).continuous
  · exact isClosed_le continuous_const (quadFormCLM x).continuous

omit [DecidableEq n] in
/-- **The Loewner order is closed.**  Scoped rather than global: the order itself
is only available after `open scoped MatrixOrder`, and a consumer outside this
namespace can enable the instance with `attribute [local instance]`. -/
theorem instOrderClosedTopology : OrderClosedTopology (Matrix n n ℝ) :=
  ⟨isClosed_le_of_isClosed_nonneg isClosed_setOf_nonneg⟩

attribute [scoped instance] instOrderClosedTopology

/-! ## Integrals of matrix-valued functions -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The Bochner integral of matrices is computed entrywise.** -/
theorem entry_integral {F : α → Matrix n n ℝ} (hF : Integrable F μ) (i j : n) :
    (∫ a, F a ∂μ) i j = ∫ a, F a i j ∂μ :=
  ((entryCLM i j).integral_comp_comm hF).symm

/-- The average of an almost everywhere positive semidefinite matrix is positive
semidefinite. -/
theorem integral_posSemidef {f : α → Matrix n n ℝ} (hf : ∀ᵐ a ∂μ, (f a).PosSemidef) :
    (∫ a, f a ∂μ).PosSemidef := by
  refine Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae ?_)
  filter_upwards [hf] with a ha using ha.nonneg

/-- Averaging is monotone for the Loewner order. -/
theorem integral_mono' {f g : α → Matrix n n ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
  integral_mono_ae hf hg h

/-- Two-sided multiplication by fixed matrices, as a continuous linear map. -/
private def conjCLM (L R : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => L * M * R
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by
        simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }

/-- Multiplying an integrable function by fixed matrices keeps it integrable. -/
theorem integrable_mul_left_mul_right (L R : Matrix n n ℝ) {F : α → Matrix n n ℝ}
    (hF : Integrable F μ) : Integrable (fun a => L * F a * R) μ :=
  (conjCLM L R).integrable_comp hF

/-- **Fixed two-sided factors pass through the integral.** -/
theorem integral_mul_left_mul_right (L R : Matrix n n ℝ) {F : α → Matrix n n ℝ}
    (hF : Integrable F μ) : ∫ a, L * F a * R ∂μ = L * (∫ a, F a ∂μ) * R :=
  (conjCLM L R).integral_comp_comm hF

/-! ## Doubled matrices -/

/-- Assembly of a doubled matrix from its four blocks, as a linear map. -/
private def fromBlocksL :
    Matrix n n ℝ × Matrix n n ℝ × Matrix n n ℝ × Matrix n n ℝ →ₗ[ℝ]
      Matrix (n ⊕ n) (n ⊕ n) ℝ where
  toFun P := Matrix.fromBlocks P.1 P.2.1 P.2.2.1 P.2.2.2
  map_add' P Q := by ext p q; cases p <;> cases q <;> rfl
  map_smul' c P := by ext p q; cases p <;> cases q <;> rfl

private def fromBlocksCLM :
    Matrix n n ℝ × Matrix n n ℝ × Matrix n n ℝ × Matrix n n ℝ →L[ℝ]
      Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  LinearMap.toContinuousLinearMap fromBlocksL

/-- A doubled matrix with integrable blocks is integrable. -/
theorem integrable_fromBlocks {A B C D : α → Matrix n n ℝ} (hA : Integrable A μ)
    (hB : Integrable B μ) (hC : Integrable C μ) (hD : Integrable D μ) :
    Integrable (fun a => Matrix.fromBlocks (A a) (B a) (C a) (D a)) μ :=
  fromBlocksCLM.integrable_comp (hA.prodMk (hB.prodMk (hC.prodMk hD)))

/-- **Doubling commutes with the integral**, the integral being entrywise. -/
theorem integral_fromBlocks {A B C D : α → Matrix n n ℝ} (hA : Integrable A μ)
    (hB : Integrable B μ) (hC : Integrable C μ) (hD : Integrable D μ) :
    ∫ a, Matrix.fromBlocks (A a) (B a) (C a) (D a) ∂μ =
      Matrix.fromBlocks (∫ a, A a ∂μ) (∫ a, B a ∂μ) (∫ a, C a ∂μ) (∫ a, D a ∂μ) := by
  have hint := integrable_fromBlocks hA hB hC hD
  ext p q
  rw [entry_integral hint]
  cases p with
  | inl i =>
      cases q with
      | inl j => exact (entry_integral hA i j).symm
      | inr j => exact (entry_integral hB i j).symm
  | inr i =>
      cases q with
      | inl j => exact (entry_integral hC i j).symm
      | inr j => exact (entry_integral hD i j).symm

/-- The trivial Schur complement: for a positive definite `Y` the doubled matrix
`(Y I; I Y⁻¹)` is positive semidefinite. -/
theorem posSemidef_fromBlocks_inv {Y : Matrix n n ℝ} (hY : Y.PosDef) :
    (Matrix.fromBlocks Y 1 1 Y⁻¹).PosSemidef := by
  have hYdet : IsUnit Y.det := isUnit_det_of_posDef hY
  have hinv : (Y⁻¹).PosDef := hY.inv
  letI : Invertible Y⁻¹ := Matrix.invertibleOfIsUnitDet _ (isUnit_det_of_posDef hinv)
  have hone : (1 : Matrix n n ℝ)ᴴ = 1 := Matrix.conjTranspose_one
  have hiff := Matrix.PosDef.fromBlocks₂₂ Y (1 : Matrix n n ℝ) hinv
  rw [hone] at hiff
  refine hiff.mpr ?_
  rw [Matrix.one_mul, Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ hYdet, sub_self]
  exact Matrix.PosSemidef.zero

/-- **Matrix Jensen**, the averaging step of the annealed primal-adjoint order:
the inverse of the average of a positive definite random matrix is below the
average of its inverse. -/
theorem inv_integral_le_integral_inv [IsProbabilityMeasure μ] {X : α → Matrix n n ℝ}
    (hX : ∀ a, (X a).PosDef) (hXint : Integrable X μ)
    (hXinv : Integrable (fun a => (X a)⁻¹) μ) (hpos : (∫ a, X a ∂μ).PosDef) :
    (∫ a, X a ∂μ)⁻¹ ≤ ∫ a, (X a)⁻¹ ∂μ := by
  -- Every realization doubles to a positive semidefinite matrix, hence so does the average.
  have hblock : (∫ a, Matrix.fromBlocks (X a) 1 1 (X a)⁻¹ ∂μ).PosSemidef :=
    integral_posSemidef (.of_forall fun a => posSemidef_fromBlocks_inv (hX a))
  have hconst : ∫ _ : α, (1 : Matrix n n ℝ) ∂μ = 1 := by
    rw [integral_const, probReal_univ, one_smul]
  rw [integral_fromBlocks hXint (integrable_const 1) (integrable_const 1) hXinv, hconst]
    at hblock
  -- Reading the Schur complement in the other corner is the conclusion.
  letI : Invertible (∫ a, X a ∂μ) := Matrix.invertibleOfIsUnitDet _ (isUnit_det_of_posDef hpos)
  have hone : (1 : Matrix n n ℝ)ᴴ = 1 := Matrix.conjTranspose_one
  have hiff := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix n n ℝ) (∫ a, (X a)⁻¹ ∂μ) hpos
  rw [hone] at hiff
  have hsub := hiff.mp hblock
  rw [Matrix.one_mul, Matrix.mul_one] at hsub
  exact Matrix.le_iff.mpr hsub

end

end HighContrast
end Homogenization
