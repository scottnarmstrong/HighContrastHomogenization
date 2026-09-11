/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootSealedOnBallTriangle
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangle

/-!
# The root at the frozen signature, with no hypothesis

`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootSealedOnBallTriangle`
inhabits the frozen statement on one named analytic hypothesis,
`ExactRootBallTriangle`, and
`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangle`
proves that hypothesis.  This module composes the two, so the frozen statement
is inhabited
at the frozen signature `(d : ℕ) (hd : 2 ≤ d)` with **no** hypothesis and no
`NeZero d` binder — the instance is derived from `hd` inside, exactly as the
frozen declaration's own signature requires.

The type below is the frozen statement's type, taken from
`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootSealedOnBallTriangle`; nothing here restates it.
-/

open Homogenization Homogenization.HighContrast
open Homogenization.HighContrast.CorrectorComposition

namespace Homogenization.HighContrast.CorrectorComposition

/-- **The frozen root statement, inhabited unconditionally.** -/
theorem polynomial_homogenization_root (d : ℕ) (hd : 2 ≤ d) :
    ∃ (cd : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ), 0 < cd ∧
      (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ (C cSrc κ : ℝ) (C₁ : ℝ → ℝ),
          0 < C ∧ 0 < cSrc ∧ 0 < κ ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
          ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)) (E :
            Homogenization.BlockMat d) (Ψ : ℝ → ℝ)
            (K : ℝ) (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
            MeasureTheory.IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
            ∃ (abar : Homogenization.Mat d) (Lpoly : ℝ) (X :
              Homogenization.HighContrast.CoeffSpace d → ℝ)
              (Phi : Homogenization.Vec d → Homogenization.HighContrast.CoeffSpace d →
                Homogenization.Vec d → ℝ)
              (gradPhi : Homogenization.Vec d → Homogenization.HighContrast.CoeffSpace d
                → Homogenization.Vec d → Homogenization.Vec d),
              1 ≤ Lpoly ∧
              Measurable X ∧
              (∀ a, 1 ≤ X a) ∧
              -- the family is linear in the slope
              (∀ (c : ℝ) (e e' : Homogenization.Vec d) (a :
                Homogenization.HighContrast.CoeffSpace d),
                gradPhi (c • e + e') a
                  =ᵐ[MeasureTheory.volume] fun x => c • gradPhi e a x + gradPhi e' a x)
                    ∧
              -- and stationary under integer translations
              (∀ (z : Fin d → ℤ) (e : Homogenization.Vec d) (a :
                Homogenization.HighContrast.CoeffSpace d),
                gradPhi e (Homogenization.HighContrast.translateCoeff z a)
                  =ᵐ[MeasureTheory.volume] fun x =>
                    gradPhi e a (x + Homogenization.Source.AKL.intTranslation z)) ∧
              -- ...length
              Lpoly ≤ (2 + Homogenization.HighContrast.aspectRatio E * K) ^ C ∧
              -- ...tail
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) + (Ψ (cSrc * t))⁻¹) ∧
              -- the symmetric part of the homogenized matrix is positive definite
              (∀ x : Homogenization.Vec d, x ≠ 0 → 0 < Homogenization.vecDot x
                (Homogenization.matVecMul (Homogenization.symmPart abar) x)) ∧
              ∃ Ωend : Set (Homogenization.HighContrast.CoeffSpace d),
                MeasurableSet Ωend ∧
                P.real Ωend = 1 ∧
                (∀ z : Fin d → ℤ, Homogenization.HighContrast.translateCoeff z ⁻¹' Ωend
                  = Ωend) ∧
                -- (1) ...dirichlet
                (∀ s₀ : ℝ, s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
                    ∀ (ρ Rad : ℝ) (U : Set (Homogenization.Vec d)),
                      (∃ j : ℤ, ∃ z : Homogenization.Vec d,
                        U = (fun x : Homogenization.Vec d =>
                          z + Homogenization.matVecMul
                            (Homogenization.HighContrast.matSqrt
                              (Homogenization.symmPart abar)) x) ''
                            Homogenization.openCubeSet
                              (Homogenization.originCube d j)) →
                      Homogenization.HighContrast.HasBallSandwich
                        (Homogenization.HighContrast.matImage
                          ((Homogenization.HighContrast.matSqrt (Homogenization.symmPart
                          abar))⁻¹) U) ρ Rad →
                      U ⊆ Homogenization.HighContrast.ellipsoid abar 1 →
                      Homogenization.HighContrast.ellipsoid abar
                          (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                        ∀ a ∈ Ωend, ∀ ε : ℝ, 0 < ε → X a ≤ ε⁻¹ →
                          ∀ g₀ : Homogenization.H1Function U,
                            (∃ Lg : ℝ, ∀ᵐ x ∂MeasureTheory.volume.restrict U,
                              |g₀.toFun x| +
                                Real.sqrt (Homogenization.vecNormSq (g₀.grad x)) ≤ Lg) →
                            Homogenization.HighContrast.hsNormSq U s₀ g₀.grad ≠ ⊤ →
                            ∀ h : Homogenization.H1Function U,
                              Homogenization.HighContrast.MemAffineH10 U g₀ h →
                              Homogenization.HighContrast.IsWeakSolutionOn (fun _ =>
                                abar) U h.grad →
                              ∀ (uFun : Homogenization.Vec d → ℝ) (uGrad :
                                Homogenization.Vec d → Homogenization.Vec d),
                                Homogenization.HighContrast.MemH1a0
                                  (Homogenization.HighContrast.scaledCoeff ε a) U
                                  (fun x => uFun x - g₀.toFun x)
                                  (fun x => uGrad x - g₀.grad x) →
                                Homogenization.HighContrast.IsWeakSolutionOn
                                  (Homogenization.HighContrast.scaledCoeff ε a) U uGrad
                                  →
                                Homogenization.HighContrast.negSobolevNorm U s₀
                                    (fun x => Homogenization.matVecMul
                                      (Homogenization.HighContrast.matSqrt
                                      (Homogenization.symmPart abar))
                                      (uGrad x - h.grad x)) +
                                  Homogenization.HighContrast.negSobolevNorm U s₀
                                    (fun x => Homogenization.matVecMul
                                      (Homogenization.HighContrast.matSqrt
                                      (Homogenization.symmPart abar))⁻¹
                                      (Homogenization.matVecMul
                                          (Homogenization.HighContrast.scaledCoeff ε a x
                                            - Homogenization.skewPart abar)
                                          (uGrad x) -
                                        Homogenization.matVecMul
                                          (Homogenization.symmPart abar)
                                          (h.grad x))) ≤
                                  ENNReal.ofReal
                                      (C₀ s₀ ρ Rad * (ε * X a) ^ κ) *
                                    Homogenization.HighContrast.hsNormSq U s₀
                                        (fun x => Homogenization.matVecMul
                                          (Homogenization.HighContrast.matSqrt
                                            (Homogenization.symmPart abar)) (g₀.grad x))
                                            ^
                                      (1 / 2 : ℝ)) ∧
                -- (2a) ...corrector.equation
                (∀ a ∈ Ωend, ∀ e : Homogenization.Vec d,
                  Homogenization.HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                    Homogenization.HighContrast.IsWeakSolutionOn (fun x => a.1 x)
                      Set.univ
                      (fun x => e + gradPhi e a x)) ∧
                -- (2b) ...corrector: the inverse-radius factor is written on
                -- each summand rather than absorbed into the constant
                (∀ a ∈ Ωend, ∀ e : Homogenization.Vec d, ∀ r : ℝ, X a ≤ r →
                  ENNReal.ofReal r⁻¹ *
                      Homogenization.HighContrast.negOneNorm
                        (Homogenization.HighContrast.ellipsoid abar r)
                        (fun x => Homogenization.matVecMul
                          (Homogenization.HighContrast.matSqrt (Homogenization.symmPart
                          abar))
                          (gradPhi e a x)) +
                    ENNReal.ofReal r⁻¹ *
                      Homogenization.HighContrast.negOneNorm
                        (Homogenization.HighContrast.ellipsoid abar r)
                        (fun x => Homogenization.matVecMul
                          (Homogenization.HighContrast.matSqrt (Homogenization.symmPart
                          abar))⁻¹
                          (Homogenization.matVecMul (a.1 x - Homogenization.skewPart abar)
                              (e + gradPhi e a x) -
                            Homogenization.matVecMul (Homogenization.symmPart abar) e)) ≤
                    ENNReal.ofReal
                      (C * Real.sqrt (Homogenization.vecDot e (Homogenization.matVecMul
                        (Homogenization.symmPart abar) e)) *
                        (r / X a) ^ (-κ))) ∧
                -- (3) ...liouville (double inclusion)
                (∀ a ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                  (∀ (v : Homogenization.Vec d → ℝ) (Dv : Homogenization.Vec d →
                    Homogenization.Vec d),
                    Homogenization.HighContrast.MemLiouvilleClass (fun x => a.1 x) ϑ v
                      Dv →
                    ∃ (e : Homogenization.Vec d) (c : ℝ),
                      v =ᵐ[MeasureTheory.volume] fun x => Homogenization.vecDot e x +
                        Phi e a x + c) ∧
                  (∀ (e : Homogenization.Vec d) (c : ℝ),
                    Homogenization.HighContrast.MemLiouvilleClass (fun x => a.1 x) ϑ
                      (fun x => Homogenization.vecDot e x + Phi e a x + c)
                      (fun x => e + gradPhi e a x))) ∧
                -- (4) ...lipschitz and (5) ...C1
                (∀ a ∈ Ωend, ∀ R : ℝ, X a ≤ R →
                  ∀ (u : Homogenization.Vec d → ℝ) (Du : Homogenization.Vec d →
                    Homogenization.Vec d),
                    Homogenization.HighContrast.MemH1a (fun x => a.1 x)
                      (Homogenization.HighContrast.ellipsoid abar R) u Du →
                    Homogenization.HighContrast.IsWeakSolutionOn (fun x => a.1 x)
                      (Homogenization.HighContrast.ellipsoid abar R) Du →
                    (∀ r : ℝ, r ∈ Set.Icc (X a) R →
                      Homogenization.HighContrast.weightedGradNorm (fun x => a.1 x)
                        (Homogenization.HighContrast.ellipsoid abar r) Du ≤
                        ENNReal.ofReal C *
                          Homogenization.HighContrast.weightedGradNorm (fun x => a.1 x)
                            (Homogenization.HighContrast.ellipsoid abar R) Du) ∧
                    (∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                      ∃ e : Homogenization.Vec d, ∀ r : ℝ, r ∈ Set.Icc (X a) R →
                        Homogenization.HighContrast.weightedGradNorm (fun x => a.1 x)
                          (Homogenization.HighContrast.ellipsoid abar r)
                            (fun x => Du x - (e + gradPhi e a x)) ≤
                          ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                            Homogenization.HighContrast.weightedGradNorm (fun x => a.1
                              x)
                              (Homogenization.HighContrast.ellipsoid abar R) Du)) :=
  polynomial_homogenization_root_of_ballTriangle d hd (@CorrectorComposition.exactRootBallTriangle d ⟨by omega⟩)

end Homogenization.HighContrast.CorrectorComposition
