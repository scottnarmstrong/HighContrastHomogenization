/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Frozen.PolynomialHomogenization
import HCPolyAudit.PolynomialHomogenization.SolutionBasic

/-!
# Bridges for the polynomial homogenization comparator, algebraic layer

The comparator challenge rebuilds from Mathlib alone every object the
polynomial homogenization theorem `t.random.homogenization` is stated with.
Most of those rebuilt objects unfold to the library ones, so the bridges below
are reflexivity; the exceptions are the inductive copies — the doubled block
matrix, the triadic cube, the block state, the two Sobolev witness records, and
the two test-function records — which are transported by field shuffling, and
the local `σ`-fields of the coefficient space, whose generators mention one of
those records and therefore agree only propositionally.

This file covers the ambient algebra, the triadic geometry, the Sobolev
witnesses, the block variational quantity and the coarse block response, and the
transport of a law along the equality of the two measurable structures.  The
remaining bridges are in `HCPolyAudit.Support.PolynomialHomogenizationBridge2`.
-/

namespace HCPoly.StatementAudit.PolynomialHomogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The doubled block algebra -/

/-- The library reading of a doubled block matrix. -/
def toBlk (A : BlockMat d) : Homogenization.BlockMat d :=
  { upperLeft := A.upperLeft
    upperRight := A.upperRight
    lowerLeft := A.lowerLeft
    lowerRight := A.lowerRight }

theorem blockMatVecMul_toBlk (A : BlockMat d) (X : BlockVec d) :
    blockMatVecMul A X = Homogenization.blockMatVecMul (toBlk A) X := rfl

theorem blockMatEntry_toBlk (A : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry A α β = Homogenization.blockMatEntry (toBlk A) α β := by
  cases α <;> cases β <;> rfl

theorem blockBasis_eq :
    (blockBasis : BlockCoord d → BlockVec d) = Homogenization.blockBasis := by
  funext α
  cases α <;> rfl

theorem blockMatLoewnerLE_toBlk (A B : BlockMat d) :
    BlockMatLoewnerLE A B ↔
      Homogenization.BlockMatLoewnerLE (toBlk A) (toBlk B) := Iff.rfl

theorem blockPosDef_toBlk (A : BlockMat d) :
    BlockPosDef A ↔ Homogenization.Book.Ch02.BlockPosDef (toBlk A) := Iff.rfl

theorem isSymmetricBlockMat_toBlk (A : BlockMat d) :
    IsSymmetricBlockMat A ↔ Homogenization.IsSymmetricBlockMat (toBlk A) := by
  constructor
  · intro h α β
    rw [← blockMatEntry_toBlk, ← blockMatEntry_toBlk]
    exact h α β
  · intro h α β
    rw [blockMatEntry_toBlk, blockMatEntry_toBlk]
    exact h α β

theorem toBlk_blockScale (c : ℝ) (A : BlockMat d) :
    toBlk (blockScale c A) =
      Homogenization.HighContrast.blockScale c (toBlk A) := rfl

theorem aspectRatio_toBlk (E : BlockMat d) :
    aspectRatio E = Homogenization.HighContrast.aspectRatio (toBlk E) := rfl

/-- Two doubled block matrices with the same entries are equal. -/
theorem blockMat_ext {A B : Homogenization.BlockMat d}
    (h : ∀ α β, Homogenization.blockMatEntry A α β =
      Homogenization.blockMatEntry B α β) : A = B := by
  obtain ⟨a₁, a₂, a₃, a₄⟩ := A
  obtain ⟨b₁, b₂, b₃, b₄⟩ := B
  have e₁ : a₁ = b₁ := by funext i j; exact h (Sum.inl i) (Sum.inl j)
  have e₂ : a₂ = b₂ := by funext i j; exact h (Sum.inl i) (Sum.inr j)
  have e₃ : a₃ = b₃ := by funext i j; exact h (Sum.inr i) (Sum.inl j)
  have e₄ : a₄ = b₄ := by funext i j; exact h (Sum.inr i) (Sum.inr j)
  subst e₁; subst e₂; subst e₃; subst e₄; rfl

/-! ## Triadic geometry -/

theorem openCubeSet_originCube_eq (d : ℕ) (j : ℤ) :
    openCubeSet (originCube d j) =
      Homogenization.openCubeSet (Homogenization.originCube d j) := rfl

theorem centeredCube_eq (d : ℕ) (m : ℤ) :
    centeredCube d m = Homogenization.HighContrast.centeredCube d m := rfl

theorem standardCell_eq (d : ℕ) (k : ℤ) (w : Fin d → ℤ) :
    standardCell d k w = Homogenization.HighContrast.standardCell d k w := rfl

theorem standardCellCenter_eq (k : ℤ) (w : Fin d → ℤ) :
    (standardCellCenter k w : Vec d) =
      Homogenization.HighContrast.standardCellCenter k w := rfl

/-! ## The Sobolev witnesses -/

/-- The library reading of an `H¹(U)` witness. -/
def toRepoH1 {U : Set (Vec d)} (u : H1Function U) : Homogenization.H1Function U :=
  { toFun := u.toFun
    grad := u.grad
    memL2 := u.memL2
    gradMemL2 := u.gradMemL2
    hasWeakGradient := u.hasWeakGradient }

/-- The challenge reading of an `H¹(U)` witness. -/
def ofRepoH1 {U : Set (Vec d)} (u : Homogenization.H1Function U) : H1Function U :=
  { toFun := u.toFun
    grad := u.grad
    memL2 := u.memL2
    gradMemL2 := u.gradMemL2
    hasWeakGradient := u.hasWeakGradient }

/-- The library reading of an `H¹₀(U)` witness. -/
def toRepoH10 {U : Set (Vec d)} (u : H10Function U) :
    Homogenization.H10Function U :=
  { toH1Function := toRepoH1 u.toH1Function
    approx := u.approx
    approx_smooth := u.approx_smooth
    approx_hasCompactSupport := u.approx_hasCompactSupport
    approx_support_subset := u.approx_support_subset
    tendsto_approx := u.tendsto_approx
    tendsto_approx_grad := u.tendsto_approx_grad }

/-- The challenge reading of an `H¹₀(U)` witness. -/
def ofRepoH10 {U : Set (Vec d)} (u : Homogenization.H10Function U) :
    H10Function U :=
  { toH1Function := ofRepoH1 u.toH1Function
    approx := u.approx
    approx_smooth := u.approx_smooth
    approx_hasCompactSupport := u.approx_hasCompactSupport
    approx_support_subset := u.approx_support_subset
    tendsto_approx := u.tendsto_approx
    tendsto_approx_grad := u.tendsto_approx_grad }

theorem isPotentialZeroTraceOn_iff {U : Set (Vec d)} (f : Vec d → Vec d) :
    IsPotentialZeroTraceOn U f ↔ Homogenization.IsPotentialZeroTraceOn U f :=
  ⟨fun ⟨u, hu⟩ => ⟨toRepoH10 u, hu⟩, fun ⟨u, hu⟩ => ⟨ofRepoH10 u, hu⟩⟩

theorem isSolenoidalZeroNormalTraceOn_iff {U : Set (Vec d)} (g : Vec d → Vec d) :
    IsSolenoidalZeroNormalTraceOn U g ↔
      Homogenization.IsSolenoidalZeroNormalTraceOn U g :=
  ⟨fun h φ => h (ofRepoH1 φ), fun h φ => h (toRepoH1 φ)⟩

/-! ## The block variational quantity and the coarse block response -/

/-- The library reading of a block state. -/
def toRepoBlockState (X : BlockState d) : Homogenization.BlockState d :=
  { potential := X.potential
    flux := X.flux }

/-- The challenge reading of a block state. -/
def ofRepoBlockState (X : Homogenization.BlockState d) : BlockState d :=
  { potential := X.potential
    flux := X.flux }

theorem isBlockMuAdmissible_iff (U : Set (Vec d)) (P : BlockVec d)
    (X : BlockState d) :
    IsBlockMuAdmissible U P X ↔
      Homogenization.IsBlockMuAdmissible U P (toRepoBlockState X) := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, (isPotentialZeroTraceOn_iff _).1 h₂, h₃,
      (isSolenoidalZeroNormalTraceOn_iff _).1 h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, (isPotentialZeroTraceOn_iff _).2 h₂, h₃,
      (isSolenoidalZeroNormalTraceOn_iff _).2 h₄⟩

theorem muValueSet_eq (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    muValueSet U P a = Homogenization.muValueSet U P a := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨toRepoBlockState X, (isBlockMuAdmissible_iff U P X).1 hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨ofRepoBlockState X,
      (isBlockMuAdmissible_iff U P (ofRepoBlockState X)).2 hX, rfl⟩

theorem Mu_eq (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    Mu U P a = Homogenization.Mu U P a := by
  unfold Mu Homogenization.Mu
  rw [muValueSet_eq]

theorem coarseBlockEntry_eq (U : Set (Vec d)) (a : CoeffField d)
    (α β : BlockCoord d) :
    coarseBlockEntry U a α β =
      Homogenization.blockMatEntry (Homogenization.coarseBlockMatrix U a) α β := by
  rw [Homogenization.HighContrast.blockMatEntry_coarseBlockMatrix]
  by_cases h : α = β
  · simp only [coarseBlockEntry, dif_pos h, if_pos h, Mu_eq, blockBasis_eq]
  · simp only [coarseBlockEntry, dif_neg h, if_neg h, Mu_eq, blockBasis_eq]

theorem toBlk_coarseBlockMatrix (U : Set (Vec d)) (a : CoeffField d) :
    toBlk (coarseBlockMatrix U a) = Homogenization.coarseBlockMatrix U a := by
  refine blockMat_ext fun α β => ?_
  rw [← blockMatEntry_toBlk]
  cases α with
  | inl i =>
      cases β with
      | inl j => exact coarseBlockEntry_eq U a (Sum.inl i) (Sum.inl j)
      | inr j => exact coarseBlockEntry_eq U a (Sum.inl i) (Sum.inr j)
  | inr i =>
      cases β with
      | inl j => exact coarseBlockEntry_eq U a (Sum.inr i) (Sum.inl j)
      | inr j => exact coarseBlockEntry_eq U a (Sum.inr i) (Sum.inr j)

theorem toBlk_coarseBlock (U : Set (Vec d)) (a : CoeffSpace d) :
    toBlk (coarseBlock U a) =
      Homogenization.HighContrast.coarseBlock U a :=
  toBlk_coarseBlockMatrix U _

/-! ## The test-function records and the local `σ`-fields -/

theorem isLocalTest_eq :
    (IsLocalTest : Set (Vec d) → (Vec d → ℝ) → Prop) =
      Homogenization.HighContrast.IsLocalTest := by
  funext U φ
  exact propext ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

theorem isLocalVecTest_eq :
    (IsLocalVecTest : Set (Vec d) → (Vec d → Vec d) → Prop) =
      Homogenization.HighContrast.IsLocalVecTest := by
  funext U ψ
  exact propext ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

theorem coeffSigma_eq (d : ℕ) (U : Set (Vec d)) :
    coeffSigma d U = Homogenization.HighContrast.coeffSigma d U := by
  unfold coeffSigma Homogenization.HighContrast.coeffSigma
  rw [isLocalTest_eq]
  rfl

theorem instMeasurableSpaceCoeffSpace_eq (d : ℕ) :
    (instMeasurableSpaceCoeffSpace d) =
      Homogenization.HighContrast.instMeasurableSpaceCoeffSpace d :=
  coeffSigma_eq d Set.univ

/-! ## Transport of a law along an equality of measurable structures -/

section Transport

variable {α β : Type*} {m₁ m₂ : MeasurableSpace α}

/-- The reading of a measure under an equality of measurable structures. -/
def castMeasure (h : m₁ = m₂) (P : @Measure α m₁) : @Measure α m₂ := h ▸ P

theorem castMeasure_real (h : m₁ = m₂) (P : @Measure α m₁) (s : Set α) :
    (castMeasure h P).real s = P.real s := by cases h; rfl

theorem castMeasure_inj (h : m₁ = m₂) (P Q : @Measure α m₁) :
    castMeasure h P = castMeasure h Q ↔ P = Q := by cases h; exact Iff.rfl

theorem castMeasure_map (h : m₁ = m₂) (P : @Measure α m₁) (f : α → α) :
    @Measure.map α α m₂ m₂ f (castMeasure h P) =
      castMeasure h (@Measure.map α α m₁ m₁ f P) := by cases h; rfl

theorem castMeasure_ae (h : m₁ = m₂) (P : @Measure α m₁) (p : α → Prop) :
    (∀ᵐ a ∂(castMeasure h P), p a) ↔ ∀ᵐ a ∂P, p a := by cases h; exact Iff.rfl

theorem isProbabilityMeasure_castMeasure (h : m₁ = m₂) (P : @Measure α m₁)
    (hP : @IsProbabilityMeasure α m₁ P) :
    @IsProbabilityMeasure α m₂ (castMeasure h P) := by cases h; exact hP

theorem measurable_of_measurableSpace_eq [MeasurableSpace β] (h : m₁ = m₂)
    {f : α → β} (hf : @Measurable α β m₁ _ f) : @Measurable α β m₂ _ f := by
  cases h; exact hf

theorem measurableSet_of_measurableSpace_eq (h : m₁ = m₂) {s : Set α}
    (hs : @MeasurableSet α m₁ s) : @MeasurableSet α m₂ s := by cases h; exact hs

theorem indep_castMeasure (h : m₁ = m₂) (n₁ n₂ : MeasurableSpace α)
    (P : @Measure α m₁) :
    @ProbabilityTheory.Indep α n₁ n₂ m₂ (castMeasure h P) ↔
      @ProbabilityTheory.Indep α n₁ n₂ m₁ P := by cases h; exact Iff.rfl

end Transport

end

end HCPoly.StatementAudit.PolynomialHomogenization
