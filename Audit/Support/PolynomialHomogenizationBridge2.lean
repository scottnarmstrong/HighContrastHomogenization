/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Audit.Support.PolynomialHomogenizationBridge1

/-!
# Bridges for the polynomial homogenization comparator, analytic layer

The analytic carriers of `t.random.homogenization` — the normalized fractional
and negative Sobolev norms, the coefficient-weighted Sobolev classes, the weak
equation and the Liouville class — are rebuilt in the challenge from Mathlib
alone.  They unfold to the library ones except where a test-function record
enters, and this file records the resulting identifications, together with the
transport of the three standing hypotheses on the law.
-/

namespace HCPoly.StatementAudit.PolynomialHomogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The positive semidefinite square root -/

theorem matSqrt_eq (M : Mat d) :
    matSqrt M = Homogenization.HighContrast.matSqrt M := rfl

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

/-! ## Transport of the law and of the three standing hypotheses -/

/-- The library reading of a law on the coefficient space. -/
def toRepoLaw (P : Measure (CoeffSpace d)) :
    @Measure (CoeffSpace d)
      (Homogenization.HighContrast.instMeasurableSpaceCoeffSpace d) :=
  castMeasure (instMeasurableSpaceCoeffSpace_eq d) P

theorem toRepoLaw_real (P : Measure (CoeffSpace d)) (s : Set (CoeffSpace d)) :
    (toRepoLaw P).real s = P.real s :=
  castMeasure_real _ _ _

theorem toRepoLaw_ae (P : Measure (CoeffSpace d)) (p : CoeffSpace d → Prop) :
    (∀ᵐ a ∂(toRepoLaw P), p a) ↔ ∀ᵐ a ∂P, p a :=
  castMeasure_ae _ _ _

theorem isProbabilityMeasure_toRepoLaw (P : Measure (CoeffSpace d))
    (hP : IsProbabilityMeasure P) : IsProbabilityMeasure (toRepoLaw P) :=
  isProbabilityMeasure_castMeasure _ _ hP

theorem isStationaryLaw_toRepoLaw {P : Measure (CoeffSpace d)}
    (h : IsStationaryLaw P) : HCPoly.Frozen.IsStationaryLaw (toRepoLaw P) := by
  intro z
  rw [toRepoLaw, castMeasure_map]
  exact (castMeasure_inj _ _ _).2 (h z)

theorem isUnitRangeLaw_toRepoLaw {P : Measure (CoeffSpace d)}
    (h : IsUnitRangeLaw P) : HCPoly.Frozen.IsUnitRangeLaw (toRepoLaw P) := by
  intro U V hU hV hUV
  rw [← coeffSigma_eq, ← coeffSigma_eq, toRepoLaw, indep_castMeasure]
  exact h U V hU hV hUV

theorem coarseEllipticityDagger_toRepoLaw {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (h : CoarseEllipticityDagger P g E Ψ K S) :
    HCPoly.Frozen.CoarseEllipticityDagger (toRepoLaw P) g (toBlk E) Ψ K S where
  g_mem := h.g_mem
  refBlock_isSymm := (isSymmetricBlockMat_toBlk E).1 h.refBlock_isSymm
  refBlock_posDef := (blockPosDef_toBlk E).1 h.refBlock_posDef
  gauge_admissible := h.gauge_admissible
  one_lt_growthWitness := h.one_lt_growthWitness
  gauge_growth := h.gauge_growth
  source_measurable :=
    measurable_of_measurableSpace_eq (instMeasurableSpaceCoeffSpace_eq d)
      h.source_measurable
  source_nonneg := h.source_nonneg
  source_tail := fun t ht => by
    rw [toRepoLaw_real]
    exact h.source_tail t ht
  coarse_bound := by
    refine (toRepoLaw_ae P _).2 ?_
    filter_upwards [h.coarse_bound] with a ha
    intro m hm k hk w hw
    have hb := (blockMatLoewnerLE_toBlk _ _).1 (ha m hm k hk w hw)
    rwa [toBlk_coarseBlock, toBlk_blockScale] at hb

end

end HCPoly.StatementAudit.PolynomialHomogenization
