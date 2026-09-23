/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup
import HCPoly.Setup.AnalyticCarriers
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.RootTheorem

/-!
# Theorem `t.random.homogenization`

Polynomial homogenization with a random microscopic source scale: one
homogenized matrix, one polynomially bounded length, one homogenization scale
with a two-part tail, and one full-probability event on which the Dirichlet
estimate, the corrector equation and estimate, the Liouville classification and
the two large-scale regularity estimates all hold for a single corrector family.
-/

/-- **Theorem `t.random.homogenization`**: the polynomial
homogenization scale for a random microscopic source scale.

**Scope.**  Two deviations from the reference text, neither of which touches any
quantitative content.  The coefficient fields are uniformly elliptic almost
everywhere, with ellipticity constants belonging to the field and entering no
estimate; `e.qualitative.ellipticity` follows from this.  The domains
carrying the Dirichlet estimate are the adapted cells of the homogenized
matrix — translates of the image of a centred triadic cube under the symmetric
square root of `s̄` — normalized to sit between two concentric adapted
ellipsoids, rather than the bounded Lipschitz domains of the reference text.
Every domain the development uses is such a cell; the normalization fixes the
domain's size relative to `s̄`, which is the scale the endpoint constant would
otherwise have to carry, and it is satisfiable at every dimension because the
window between the two ellipsoids has triadic ratio three.
Every quantitative object below — `Π`, the gauge and its growth witness, the
homogenized matrix, the homogenization length and its tail, and every
dimensional constant and exponent — is unchanged by either.

**The centering convention of the flux displays.**  The two flux differences
below — in the Dirichlet estimate and in the corrector estimate — are written
for the skew-centered field: the constant skew part of the homogenized matrix is
subtracted from the coefficient field, and the homogenized matrix enters through
its symmetric part.  This is the standing convention under which a coefficient
field and its antisymmetric part are read modulo a constant antisymmetric
matrix.  It is the form the argument establishes, a constant skew part changing
neither the solutions nor the coarse-grained blocks; and it is the form that is
invariant under that recentering, which the displays written with the full
homogenized matrix are not.

**Valuation.**  All norms and energies are valued in `ℝ≥0∞`, so that each
estimate is an assertion about the quantity the reference text writes rather
than about a totalized integral that vanishes when that quantity is infinite.

**Constants.**  The endpoint constant of the Dirichlet estimate depends on
nothing but the dimension, the regularity exponent, and the shape of the adapted
domain `s̄^{-1/2}U` — the radii of concentric balls trapping it.  That is the
dependence the reference text records for it, and its binder accordingly stands
outside the exponent and outside the law.

Two separate things stand behind that reading, and they should not be confused.
Writing the flux difference for the skew-centered field removes one obstruction
to it: a constant skew part of the homogenized matrix is seen by no other datum
of the statement, and it moves the difference written with the full homogenized
matrix while leaving the centered one fixed.  That is what makes the printed
dependence list available to write down; it is not what makes it true.  What a
proof must use for the rest is the bound on the length below.  A law that is
badly conditioned — of large contrast, strongly anisotropic, or carrying a large
source scale — pays for it in the reference aspect ratio and the growth witness,
and the length bound lets the homogenization scale, and with it the largest
admissible microscale, absorb exactly that; the estimate is read only below that
scale.  A proof of this theorem has to honour that dependency, and the statement
is what expresses it.

The two radii enter only through their ratio.  Dilating the coefficient field
and the homogenized matrix together leaves the domain condition exactly fixed,
slides both radii along a common ray, and multiplies both sides of the estimate
by the same factor; so a constant depending on the two radii separately carries
no more than one depending on their ratio, which is the dimensionless datum the
reference text's own condition on the domain records.

The constants `C`, `C_0` and `C_1` are asserted positive; the reference text
asserts only their finiteness, and positivity is a normalization, every
occurrence of each being weakened by increasing it.

**Measurability.**  The three membership classes below carry the measurability
of the function and of its gradient field that their printed counterparts —
completions of smooth functions in a norm — presuppose.  Without it the relation
that ties a function to its weak gradient compares integrals that may each fail
to converge, and a pair on which they both fail satisfies it for no reason;
whether the wider class actually contains such a pair is a question about sets
of inner measure zero, and is not settled here.  Two
consequences are worth stating.  The second inclusion of the Liouville clause is
the only place this statement says anything about the measurability of the
corrector family.  And the corrector equation, read on its own, does not exclude
such a pair: what excludes it is that same inclusion, which puts the corrector
in the local class.

**Approximants.**  The coefficient-weighted spaces are closures under globally
smooth approximants, where the reference text closes the functions smooth on the
domain.  The two readings are recorded as distinct because the Liouville clause
states a double inclusion, in which the class occurs in both directions.  On a
bounded convex domain a function smooth on the domain agrees, after a dilation
towards an interior point, with a globally smooth function on the whole closure,
so the two readings are separated only by the continuity of that dilation in the
norm.

The invariance of `Ω_end` under integer translations is proved with the theorem
and is carried in the conclusion. -/

theorem HCPoly.Frozen.polynomial_homogenization_random_source
    (d : ℕ) (hd : 2 ≤ d) :
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
                              (Homogenization.HighContrast.ellipsoid abar R) Du))
    := by
  exact Homogenization.HighContrast.CorrectorComposition.polynomial_homogenization_root d hd
