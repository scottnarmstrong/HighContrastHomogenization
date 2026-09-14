/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPolyAudit.Support.UniformHomogenizationBridge

/-!
# The uniform homogenization comparator solution

The theorem of `HCPolyAudit.UniformHomogenization.Challenge`, proved from the library
theorem through the bridges of `HCPolyAudit.Support.UniformHomogenizationBridge`.  The
statement below is the challenge statement word for word.
-/

namespace HCPoly.StatementAudit.UniformHomogenization

open MeasureTheory

noncomputable section

/-- **Quantitative homogenization under uniform ellipticity**
(`t.uniform.homogenization`), proved from the library theorem. -/
theorem uniform_homogenization
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (κ C : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ),
      0 < κ ∧ 0 < C ∧ (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
      ∀ lam Lam : ℝ, 0 < lam → lam ≤ 1 → 1 ≤ Lam →
        ∀ P : MeasureTheory.Measure (CoeffSpace d),
          MeasureTheory.IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          -- almost sure `(λ, Λ)`-ellipticity, `e.uniform.ellipticity`
          (∀ᵐ a ∂P, ∀ᵐ x ∂MeasureTheory.volume,
            IsEllipticMatrix lam Lam (a.1 x)) →
          ∃ (abar : Mat d) (X : CoeffSpace d → ℝ)
            (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            Measurable X ∧
            (∀ a, 1 ≤ X a) ∧
            -- the family is linear in the slope
            (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
              gradPhi (c • e + e') a
                =ᵐ[MeasureTheory.volume] fun x =>
                  c • gradPhi e a x + gradPhi e' a x) ∧
            -- and stationary under integer translations
            (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
              gradPhi e (translateCoeff z a)
                =ᵐ[MeasureTheory.volume] fun x =>
                  gradPhi e a (x + intTranslation z)) ∧
            -- the tail of the homogenization scale, `e.uniform.scale.tail`
            (∀ t : ℝ, 1 ≤ t →
              P.real {a | C * (2 + Lam / lam) ^ C * t ≤ X a} ≤
                Real.exp (-(t ^ (d : ℝ)))) ∧
            -- the symmetric part of the homogenized matrix is positive definite
            (∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
            ∃ Ωend : Set (CoeffSpace d),
              MeasurableSet Ωend ∧
              P.real Ωend = 1 ∧
              (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
              -- (1) the Dirichlet estimate, in the homogeneous negative-Sobolev
              -- form of `t.random.homogenization` on the adapted cells
              (∀ s₀ : ℝ, s₀ ∈ Set.Ico (1 / 4 : ℝ) (1 / 2 : ℝ) →
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
              -- (2a) the corrector equation
              (∀ a ∈ Ωend, ∀ e : Vec d,
                HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                  IsWeakSolutionOn (fun x => a.1 x) Set.univ
                    (fun x => e + gradPhi e a x)) ∧
              -- (2b) the corrector estimate, with the inverse-radius factor
              -- written on each summand rather than absorbed into the constant
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
              -- (3) the Liouville classification, as a double inclusion
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
              -- (4) the large-scale energy estimate `e.uniform.energy` and
              -- (5) the first-order approximation, both on the ellipsoids
              -- `e.homogenized.ellipsoids`
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
  obtain ⟨κ, C, C₀, C₁, hκ, hC, hC₀, hC₁, hmain⟩ :=
    HCPoly.uniform_homogenization d hd
  refine ⟨κ, C, C₀, C₁, hκ, hC, hC₀, hC₁, ?_⟩
  intro lam Lam hlam hlamOne hLam P hP hstat hunit hell
  obtain ⟨abar, X, Phi, gradPhi, hXm, hX1, hlin, hstatPhi, htail, hposd,
      Ωend, hΩm, hΩ1, hΩinv, hdir, hceq, hcest, hliou, hreg⟩ :=
    hmain lam Lam hlam hlamOne hLam (toRepoLaw P)
      (isProbabilityMeasure_toRepoLaw P hP) (isStationaryLaw_toRepoLaw hstat)
      (isUnitRangeLaw_toRepoLaw hunit) ((toRepoLaw_ae P _).2 hell)
  refine ⟨abar, X, Phi, gradPhi, ?_, hX1, hlin, hstatPhi, ?_, hposd,
    Ωend, ?_, ?_, hΩinv, ?_, ?_, ?_, ?_, ?_⟩
  · exact measurable_of_measurableSpace_eq
      (instMeasurableSpaceCoeffSpace_eq d).symm hXm
  · intro t ht
    rw [← toRepoLaw_real]
    exact htail t ht
  · exact measurableSet_of_measurableSpace_eq
      (instMeasurableSpaceCoeffSpace_eq d).symm hΩm
  · exact (toRepoLaw_real P Ωend).symm.trans hΩ1
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

end HCPoly.StatementAudit.UniformHomogenization
