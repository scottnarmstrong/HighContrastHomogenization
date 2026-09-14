/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.MainResults
import HCPolyAudit.UniformHomogenization.SolutionBasic

/-!
# Bridges for the uniform homogenization comparator

The comparator challenge rebuilds from Mathlib alone every object the uniformly
elliptic homogenization theorem `t.uniform.homogenization` is stated with.  Most
of those rebuilt objects unfold to the library ones, so the bridges below are
reflexivity; the exceptions are the inductive copies — the two Sobolev witness
records and the two test-function records — which are transported by field
shuffling, and the local `σ`-fields of the coefficient space, whose generators
mention one of those records and therefore agree only propositionally.

The resulting equality of measurable structures on the coefficient space is an
equality of values, so a law is read across it; the transport commutes with
`Measure.map`, `Measure.real`, the almost-everywhere filter,
`IsProbabilityMeasure`, `Measurable`, `MeasurableSet` and independence, and the
two standing hypotheses on the law travel with it.
-/

namespace HCPoly.StatementAudit.UniformHomogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The scalar Loewner bound and the positive semidefinite square root -/

theorem specBound_eq (M : Mat d) :
    specBound M = Homogenization.HighContrast.specBound M := rfl

theorem matSqrt_eq (M : Mat d) :
    matSqrt M = Homogenization.HighContrast.matSqrt M := rfl

/-! ## Uniform ellipticity of a matrix -/

theorem isEllipticMatrix_iff (lam Lam : ℝ) (A : Mat d) :
    IsEllipticMatrix lam Lam A ↔ Homogenization.IsEllipticMatrix lam Lam A :=
  Iff.rfl

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

/-! ## Weak solutions, dual norms, and the weighted classes -/

theorem isWeakSolutionOn_iff (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) :
    IsWeakSolutionOn b V F ↔
      Homogenization.HighContrast.IsWeakSolutionOn b V F := by
  unfold IsWeakSolutionOn Homogenization.HighContrast.IsWeakSolutionOn
  rw [isLocalTest_eq]
  rfl

theorem negSobolevNorm_eq (V : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) :
    negSobolevNorm V s F = Homogenization.HighContrast.negSobolevNorm V s F := by
  unfold negSobolevNorm Homogenization.HighContrast.negSobolevNorm
  rw [isLocalVecTest_eq]
  rfl

theorem negOneNorm_eq (V : Set (Vec d)) (F : Vec d → Vec d) :
    negOneNorm V F = Homogenization.HighContrast.negOneNorm V F := by
  unfold negOneNorm Homogenization.HighContrast.negOneNorm
  rw [isLocalVecTest_eq]
  rfl

theorem skewFluxDualNorm_eq (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) :
    skewFluxDualNorm b V F =
      Homogenization.HighContrast.skewFluxDualNorm b V F := by
  unfold skewFluxDualNorm Homogenization.HighContrast.skewFluxDualNorm
  rw [isLocalTest_eq]
  rfl

theorem memH1a_iff (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) :
    MemH1a b V u Du ↔ Homogenization.HighContrast.MemH1a b V u Du := by
  unfold MemH1a Homogenization.HighContrast.MemH1a
  simp only [skewFluxDualNorm_eq]
  rfl

theorem memH1a0_iff (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) :
    MemH1a0 b V u Du ↔ Homogenization.HighContrast.MemH1a0 b V u Du := by
  unfold MemH1a0 Homogenization.HighContrast.MemH1a0
  simp only [skewFluxDualNorm_eq, isLocalTest_eq]
  rfl

theorem memLiouvilleClass_iff (b : CoeffField d) (ϑ : ℝ) (v : Vec d → ℝ)
    (Dv : Vec d → Vec d) :
    MemLiouvilleClass b ϑ v Dv ↔
      Homogenization.HighContrast.MemLiouvilleClass b ϑ v Dv := by
  unfold MemLiouvilleClass Homogenization.HighContrast.MemLiouvilleClass
  rw [isWeakSolutionOn_iff]
  rfl

theorem memAffineH10_iff {U : Set (Vec d)} (g₀ h : H1Function U) :
    MemAffineH10 U g₀ h ↔
      Homogenization.HighContrast.MemAffineH10 U (toRepoH1 g₀) (toRepoH1 h) :=
  ⟨fun ⟨w, h₁, h₂⟩ => ⟨toRepoH10 w, h₁, h₂⟩,
    fun ⟨w, h₁, h₂⟩ => ⟨ofRepoH10 w, h₁, h₂⟩⟩

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

/-! ## Transport of the law and of the standing hypotheses -/

/-- The library reading of a law on the coefficient space. -/
def toRepoLaw (P : Measure (CoeffSpace d)) :
    @Measure (CoeffSpace d)
      (Homogenization.HighContrast.instMeasurableSpaceCoeffSpace d) :=
  castMeasure (instMeasurableSpaceCoeffSpace_eq d) P

theorem toRepoLaw_real (P : Measure (CoeffSpace d)) (s : Set (CoeffSpace d)) :
    (toRepoLaw P).real s = P.real s :=
  castMeasure_real _ _ _

theorem toRepoLaw_ae (P : Measure (CoeffSpace d)) (p : CoeffSpace d → Prop) :
    Filter.Eventually p
        (@MeasureTheory.ae (CoeffSpace d)
          (@Measure (CoeffSpace d) (Homogenization.HighContrast.instMeasurableSpaceCoeffSpace d))
          (@Measure.instFunLike (CoeffSpace d)
            (Homogenization.HighContrast.instMeasurableSpaceCoeffSpace d))
          (@Measure.instOuterMeasureClass (CoeffSpace d)
            (Homogenization.HighContrast.instMeasurableSpaceCoeffSpace d))
          (toRepoLaw P)) ↔
      ∀ᵐ a ∂P, p a :=
  castMeasure_ae _ _ _

theorem isProbabilityMeasure_toRepoLaw (P : Measure (CoeffSpace d))
    (hP : IsProbabilityMeasure P) : IsProbabilityMeasure (toRepoLaw P) :=
  isProbabilityMeasure_castMeasure _ _ hP

theorem isStationaryLaw_toRepoLaw {P : Measure (CoeffSpace d)}
    (h : IsStationaryLaw P) : HCPoly.Frozen.IsStationaryLaw (toRepoLaw P) := by
  intro z
  exact (castMeasure_map (instMeasurableSpaceCoeffSpace_eq d) P (translateCoeff z)).trans
    ((castMeasure_inj (instMeasurableSpaceCoeffSpace_eq d) _ _).2 (h z))

theorem isUnitRangeLaw_toRepoLaw {P : Measure (CoeffSpace d)}
    (h : IsUnitRangeLaw P) : HCPoly.Frozen.IsUnitRangeLaw (toRepoLaw P) := by
  intro U V hU hV hUV
  have hcast := (indep_castMeasure (instMeasurableSpaceCoeffSpace_eq d) (coeffSigma d U)
    (coeffSigma d V) P).2 (h U V hU hV hUV)
  rwa [coeffSigma_eq d U, coeffSigma_eq d V] at hcast

end

end HCPoly.StatementAudit.UniformHomogenization
