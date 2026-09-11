/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Audit.Support.PolynomialHomogenizationBridge2

/-!
# The polynomial homogenization comparator solution

The theorem of `Audit.PolynomialHomogenization.Challenge`, proved from the
library theorem through the bridges of
`Audit.Support.PolynomialHomogenizationBridge1` and
`Audit.Support.PolynomialHomogenizationBridge2`.  The statement below is the
challenge statement word for word.
-/

namespace HCPoly.StatementAudit.PolynomialHomogenization

open MeasureTheory

noncomputable section

/-- **Polynomial homogenization with a random microscopic source scale**
(`t.random.homogenization`), proved from the library theorem. -/
theorem polynomial_homogenization
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (cd : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ), 0 < cd ∧
      (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ (C cSrc κ : ℝ) (C₁ : ℝ → ℝ),
          0 < C ∧ 0 < cSrc ∧ 0 < κ ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
          ∀ (P : MeasureTheory.Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ)
            (K : ℝ) (S : CoeffSpace d → ℝ),
            MeasureTheory.IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P g E Ψ K S →
            ∃ (abar : Mat d) (Lpoly : ℝ) (X : CoeffSpace d → ℝ)
              (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
              (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
              1 ≤ Lpoly ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              -- the family is linear in the slope
              (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
                gradPhi (c • e + e') a
                  =ᵐ[MeasureTheory.volume] fun x => c • gradPhi e a x + gradPhi e' a x)
                    ∧
              -- and stationary under integer translations
              (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
                gradPhi e (translateCoeff z a)
                  =ᵐ[MeasureTheory.volume] fun x =>
                    gradPhi e a (x + intTranslation z)) ∧
              -- ...length
              Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
              -- ...tail
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) + (Ψ (cSrc * t))⁻¹) ∧
              -- the symmetric part of the homogenized matrix is positive definite
              (∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
              ∃ Ωend : Set (CoeffSpace d),
                MeasurableSet Ωend ∧
                P.real Ωend = 1 ∧
                (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
                -- (1) ...dirichlet
                (∀ s₀ : ℝ, s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
                    ∀ (ρ Rad : ℝ) (U : Set (Vec d)),
                      (∃ j : ℤ, ∃ z : Vec d,
                        U = (fun x : Vec d =>
                          z + matVecMul (matSqrt (symmPart abar)) x) ''
                            openCubeSet (originCube d j)) →
                      HasBallSandwich
                        (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad →
                      U ⊆ ellipsoid abar 1 →
                      ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                        ∀ a ∈ Ωend, ∀ ε : ℝ, 0 < ε → X a ≤ ε⁻¹ →
                          ∀ g₀ : H1Function U,
                            (∃ Lg : ℝ, ∀ᵐ x ∂MeasureTheory.volume.restrict U,
                              |g₀.toFun x| +
                                Real.sqrt (vecNormSq (g₀.grad x)) ≤ Lg) →
                            hsNormSq U s₀ g₀.grad ≠ ⊤ →
                            ∀ h : H1Function U,
                              MemAffineH10 U g₀ h →
                              IsWeakSolutionOn (fun _ => abar) U h.grad →
                              ∀ (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d),
                                MemH1a0 (scaledCoeff ε a) U
                                  (fun x => uFun x - g₀.toFun x)
                                  (fun x => uGrad x - g₀.grad x) →
                                IsWeakSolutionOn (scaledCoeff ε a) U uGrad →
                                negSobolevNorm U s₀
                                    (fun x => matVecMul (matSqrt (symmPart abar))
                                      (uGrad x - h.grad x)) +
                                  negSobolevNorm U s₀
                                    (fun x => matVecMul
                                      (matSqrt (symmPart abar))⁻¹
                                      (matVecMul
                                          (scaledCoeff ε a x - skewPart abar)
                                          (uGrad x) -
                                        matVecMul (symmPart abar) (h.grad x))) ≤
                                  ENNReal.ofReal
                                      (C₀ s₀ ρ Rad * (ε * X a) ^ κ) *
                                    hsNormSq U s₀
                                        (fun x => matVecMul
                                          (matSqrt (symmPart abar)) (g₀.grad x)) ^
                                      (1 / 2 : ℝ)) ∧
                -- (2a) ...corrector.equation
                (∀ a ∈ Ωend, ∀ e : Vec d,
                  HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                    IsWeakSolutionOn (fun x => a.1 x) Set.univ
                      (fun x => e + gradPhi e a x)) ∧
                -- (2b) ...corrector: the inverse-radius factor is written on
                -- each summand rather than absorbed into the constant
                (∀ a ∈ Ωend, ∀ e : Vec d, ∀ r : ℝ, X a ≤ r →
                  ENNReal.ofReal r⁻¹ *
                      negOneNorm (ellipsoid abar r)
                        (fun x => matVecMul (matSqrt (symmPart abar))
                          (gradPhi e a x)) +
                    ENNReal.ofReal r⁻¹ *
                      negOneNorm (ellipsoid abar r)
                        (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                          (matVecMul (a.1 x - skewPart abar)
                              (e + gradPhi e a x) -
                            matVecMul (symmPart abar) e)) ≤
                    ENNReal.ofReal
                      (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
                        (r / X a) ^ (-κ))) ∧
                -- (3) ...liouville (double inclusion)
                (∀ a ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                  (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
                    MemLiouvilleClass (fun x => a.1 x) ϑ v Dv →
                    ∃ (e : Vec d) (c : ℝ),
                      v =ᵐ[MeasureTheory.volume] fun x => vecDot e x +
                        Phi e a x + c) ∧
                  (∀ (e : Vec d) (c : ℝ),
                    MemLiouvilleClass (fun x => a.1 x) ϑ
                      (fun x => vecDot e x + Phi e a x + c)
                      (fun x => e + gradPhi e a x))) ∧
                -- (4) ...lipschitz and (5) ...C1
                (∀ a ∈ Ωend, ∀ R : ℝ, X a ≤ R →
                  ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                    MemH1a (fun x => a.1 x) (ellipsoid abar R) u Du →
                    IsWeakSolutionOn (fun x => a.1 x) (ellipsoid abar R) Du →
                    (∀ r : ℝ, r ∈ Set.Icc (X a) R →
                      weightedGradNorm (fun x => a.1 x) (ellipsoid abar r) Du ≤
                        ENNReal.ofReal C *
                          weightedGradNorm (fun x => a.1 x)
                            (ellipsoid abar R) Du) ∧
                    (∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                      ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc (X a) R →
                        weightedGradNorm (fun x => a.1 x) (ellipsoid abar r)
                            (fun x => Du x - (e + gradPhi e a x)) ≤
                          ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                            weightedGradNorm (fun x => a.1 x)
                              (ellipsoid abar R) Du)) := by
  obtain ⟨cd, C₀, hcd, hC₀, hmain⟩ :=
    HCPoly.Frozen.polynomial_homogenization_random_source d hd
  refine ⟨cd, C₀, hcd, hC₀, ?_⟩
  intro g hg
  obtain ⟨C, cSrc, κ, C₁, hC, hcSrc, hκ, hC₁, hmain⟩ := hmain g hg
  refine ⟨C, cSrc, κ, C₁, hC, hcSrc, hκ, hC₁, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag
  obtain ⟨abar, Lpoly, X, Phi, gradPhi, hL1, hXm, hX1, hlin, hstatPhi, hLen, htail,
      hposd, Ωend, hΩm, hΩ1, hΩinv, hdir, hceq, hcest, hliou, hreg⟩ :=
    hmain (toRepoLaw P) (toBlk E) Ψ K S (isProbabilityMeasure_toRepoLaw P hP)
      (isStationaryLaw_toRepoLaw hstat) (isUnitRangeLaw_toRepoLaw hunit)
      (coarseEllipticityDagger_toRepoLaw hdag)
  refine ⟨abar, Lpoly, X, Phi, gradPhi, hL1, ?_, hX1, hlin, hstatPhi, ?_, ?_, hposd,
    Ωend, ?_, ?_, hΩinv, ?_, ?_, ?_, ?_, ?_⟩
  · exact measurable_of_measurableSpace_eq
      (instMeasurableSpaceCoeffSpace_eq d).symm hXm
  · rw [aspectRatio_toBlk]
    exact hLen
  · intro t ht
    rw [← toRepoLaw_real]
    exact htail t ht
  · exact measurableSet_of_measurableSpace_eq
      (instMeasurableSpaceCoeffSpace_eq d).symm hΩm
  · rw [← toRepoLaw_real]
    exact hΩ1
  · intro s₀ hs₀ ρ Rad U hUform hsand hUin hinU a ha ε hε hXε g₀ hg₀bd hg₀fin
      h hh hwh uFun uGrad hmem hsol
    rw [negSobolevNorm_eq, negSobolevNorm_eq]
    exact hdir s₀ hs₀ ρ Rad U hUform hsand hUin hinU a ha ε hε hXε (toRepoH1 g₀)
      hg₀bd hg₀fin (toRepoH1 h) ((memAffineH10_iff g₀ h).1 hh)
      ((isWeakSolutionOn_iff _ _ _).1 hwh) uFun uGrad
      ((memH1a0_iff _ _ _ _).1 hmem) ((isWeakSolutionOn_iff _ _ _).1 hsol)
  · intro a ha e
    exact ⟨(hceq a ha e).1, (isWeakSolutionOn_iff _ _ _).2 (hceq a ha e).2⟩
  · intro a ha e r hr
    rw [negOneNorm_eq, negOneNorm_eq]
    exact hcest a ha e r hr
  · intro a ha ϑ hϑ
    refine ⟨fun v Dv hv =>
      (hliou a ha ϑ hϑ).1 v Dv ((memLiouvilleClass_iff _ _ _ _).1 hv), ?_⟩
    intro e c
    exact (memLiouvilleClass_iff _ _ _ _).2 ((hliou a ha ϑ hϑ).2 e c)
  · intro a ha R hR u Du hmemu hsolu
    exact ⟨(hreg a ha R hR u Du ((memH1a_iff _ _ _ _).1 hmemu)
        ((isWeakSolutionOn_iff _ _ _).1 hsolu)).1,
      (hreg a ha R hR u Du ((memH1a_iff _ _ _ _).1 hmemu)
        ((isWeakSolutionOn_iff _ _ _).1 hsolu)).2⟩

end

end HCPoly.StatementAudit.PolynomialHomogenization
