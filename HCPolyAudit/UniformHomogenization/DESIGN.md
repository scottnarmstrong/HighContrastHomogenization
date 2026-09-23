# Comparator surface for `t.uniform.homogenization`

`HCPolyAudit/UniformHomogenization/` carries a Mathlib-only comparator challenge for
Theorem C of the high-contrast polynomial-scale paper, and a solution proving
the byte-identical statement from the library.

| File | Role |
| --- | --- |
| `UniformHomogenization/Challenge.lean` | `import Mathlib` only; rebuilds the vocabulary, states the theorem, leaves one `sorry` |
| `UniformHomogenization/SolutionBasic.lean` | verbatim copy of the challenge vocabulary, `import Mathlib` only |
| `Support/UniformHomogenizationBridge.lean` | identifies the rebuilt vocabulary with the library objects |
| `UniformHomogenization/Solution.lean` | proves the byte-identical statement |
| `UniformHomogenization/comparator.json` | comparator configuration |
| `check_standalone.sh` | elaborates one file with the project's Lean options |

## The checked statement

```lean
theorem HCPoly.StatementAudit.UniformHomogenization.uniform_homogenization
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (κ C : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ),
      0 < κ ∧ 0 < C ∧ (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
      ∀ lam Lam : ℝ, 0 < lam → lam ≤ 1 → 1 ≤ Lam →
        ∀ P : Measure (CoeffSpace d), IsProbabilityMeasure P →
          IsStationaryLaw P → IsUnitRangeLaw P →
          (∀ᵐ a ∂P, ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (a.1 x)) →
          ∃ (abar : Mat d) (X : CoeffSpace d → ℝ)
            (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            Measurable X ∧ (∀ a, 1 ≤ X a) ∧
            -- linearity in the slope and stationarity of the corrector family
            … ∧
            -- the tail `e.uniform.scale.tail`
            (∀ t : ℝ, 1 ≤ t →
              P.real {a | C * (2 + Lam / lam) ^ C * t ≤ X a} ≤
                Real.exp (-(t ^ (d : ℝ)))) ∧
            (∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
            ∃ Ωend : Set (CoeffSpace d),
              MeasurableSet Ωend ∧ P.real Ωend = 1 ∧
              (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
              -- the Dirichlet estimate, the corrector equation and estimate, the
              -- Liouville classification, `e.uniform.energy` and the first-order
              -- approximation
              …
```

Every name is the challenge's own definition; the elided clauses are written out
in full in `Challenge.lean`. The paper's Theorem C prints the forced `L²`
Dirichlet and large-scale energy estimates. The formal statement also exports
corrector, Liouville and approximation clauses from Theorem D.

## Definition provenance

| Challenge declaration | Library source |
| --- | --- |
| `Vec`, `Mat`, `vecDot`, `vecNormSq`, `matVecMul`, `symmPart`, `skewPart` | `Homogenization/Ambient/Basic.lean` |
| `MatLoewnerLE` | `Homogenization/Ambient/BlockMatrix.lean` |
| `CoeffField`, `IsEllipticMatrix` | `Homogenization/Ambient/CoefficientField.lean` |
| `AEField`, `intTranslation`, `translateField`, `supDist` | `Homogenization/Probability/Source/AKL.lean` |
| `IsAELocallyUniformlyElliptic`, `AEUniformlyEllipticField`, `CoeffSpace`, `translateCoeff` | `HCPoly/Setup/CoefficientSpace.lean` |
| `IsLocalTest`, `coeffPairing`, `coeffSigma`, `instMeasurableSpaceCoeffSpace`, `UnitSeparated` | `HCPoly/Setup/LocalSigmaFields.lean` |
| `TriadicCube`, `cubeScaleFactor`, `openCubeSet`, `originCube` | `Homogenization/Geometry/TriadicCube.lean` |
| `specBound`, `matSqrt` | `HCPoly/Setup/BlockAlgebra.lean` |
| `basisVec`, `HasWeakPartialDerivOn`, `HasWeakGradientOn` | `Homogenization/Sobolev/WeakDerivatives.lean` |
| `MemL2On`, `GradMemL2On`, `H1Function`, `H10Function` | `Homogenization/Sobolev/H1/Definitions.lean` |
| `volumeAverage` | `Homogenization/CoarseGraining/Definitions.lean` |
| `scaledCoeff`, `euclideanBallAt`, `euclideanBall`, `smoothGrad`, `IsLocalVecTest`, `eVolumeAverage`, `normalizedL2Norm`, `weightedGradNorm`, `fracSeminormSq`, `hsNormSq`, `h1NormSq`, `dualPairing`, `negSobolevNorm`, `negOneNorm`, `sEnergyOn`, `h1sNormSqOn`, `skewFluxPairing`, `skewFluxDualNorm`, `IsMeasurableGradientPair`, `MemH1a`, `MemH1a0`, `MemH1sLoc`, `IsWeakSolutionOn`, `MemLiouvilleClass`, `MemAffineH10` | `HCPoly/Setup/AnalyticCarriers.lean` |
| `matImage`, `HasBallSandwich`, `ellipsoid` | `HCPoly/Setup/Geometry.lean` |
| `IsStationaryLaw`, `IsUnitRangeLaw` | `HCPoly/Frozen/{Stationarity,UnitRange}.lean` |

The challenge carries no declaration outside this table: a dependency walk of
the theorem's statement closure reaches every one of them, and nothing else.

## Bridge inventory

**Definitionally shared.**  The following rebuilt objects unfold to the library
objects, so the identification is `rfl` (checked in the bridge file, or used
silently where the two terms are interchangeable):

* the carrier `CoeffSpace d`, since `Vec`, `Mat` and the a.e.-quotient are
  Mathlib types and every predicate in the subtype is a chain of plain `def`s
  with identical bodies;
* `IsEllipticMatrix`, `MatLoewnerLE`, `specBound`, `matSqrt` (`specBound_eq`,
  `matSqrt_eq`, `isEllipticMatrix_iff`);
* `translateField`, `translateCoeff` (the ellipticity side condition is a
  proof, hence definitionally irrelevant), `intTranslation`, `supDist`,
  `UnitSeparated`;
* `coeffPairing`, hence the generating statistics of the local σ-fields;
* `openCubeSet (originCube d j)`: the cube records are structure literals, so
  their projections reduce;
* `scaledCoeff`, `volumeAverage`, `eVolumeAverage`, `normalizedL2Norm`,
  `weightedGradNorm`, `fracSeminormSq`, `hsNormSq`, `h1NormSq`, `dualPairing`,
  `sEnergyOn`, `h1sNormSqOn`, `skewFluxPairing`;
* `matImage`, `HasBallSandwich`, `ellipsoid`, `euclideanBallAt`,
  `euclideanBall`, `smoothGrad`;
* `HasWeakPartialDerivOn`, `HasWeakGradientOn`, `MemL2On`, `GradMemL2On`,
  `IsMeasurableGradientPair`, `MemH1sLoc`.

**Structure copies.**  `H1Function`, `H10Function` and `TriadicCube` are
inductive types, so the rebuilt copies are new types.  Each field of each copy
has a type definitionally equal to the corresponding library field, so both
conversion directions are single constructor applications
(`toRepoH1`/`ofRepoH1`, `toRepoH10`/`ofRepoH10`).  `TriadicCube` never needs a
conversion: it is consumed only through `openCubeSet` of a structure literal.

**The test-function records.**  `IsLocalTest` and `IsLocalVecTest` are
one-constructor records, so the two copies agree only propositionally
(`isLocalTest_eq`, `isLocalVecTest_eq`).  Every object quantifying over them is
identified by rewriting along those equalities: `IsWeakSolutionOn`,
`negSobolevNorm`, `negOneNorm`, `skewFluxDualNorm`, and through the last of
these `MemH1a` and `MemH1a0`, then `MemLiouvilleClass`.  `MemAffineH10`
quantifies over an `H¹₀` witness existentially, so it is identified by the two
constructor conversions.

**The measurable structure.**  Because the generating family of `coeffSigma`
mentions `IsLocalTest`, the resulting equality
`coeffSigma d U = Homogenization.HighContrast.coeffSigma d U`, at `U = univ`,
is an equality of the two `MeasurableSpace (CoeffSpace d)` instances rather
than a definitional unfolding.  Laws are transported along it by `castMeasure`,
and the transport commutes with `Measure.map`, `Measure.real`, the
almost-everywhere filter, `IsProbabilityMeasure`, `Measurable`, `MeasurableSet`
and `ProbabilityTheory.Indep`.  These are all proved by substituting the
instance equality.  The two standing hypotheses on the law travel with it
(`isStationaryLaw_toRepoLaw`, `isUnitRangeLaw_toRepoLaw`), and so does the
almost sure ellipticity hypothesis, through `toRepoLaw_ae`.

## Presentation deltas

1. **The Dirichlet clause.**  It is the homogeneous negative-Sobolev estimate of
   `t.random.homogenization`, read on the adapted cells of the homogenized
   matrix, not the `L²` estimate `e.uniform.dirichlet` with a forcing term on the
   ellipsoids `e.homogenized.ellipsoids`; the reference text deduces the latter
   from the former by a separate duality argument, which is not formalized.  The
   tolerance `δ` of that estimate is accordingly absent, and the endpoint
   constant is the shape constant of `t.random.homogenization`.
2. **Adapted domains.**  The domains carrying the Dirichlet estimate are the
   adapted cells of the homogenized matrix — translates of the image of a centred
   triadic cube under the symmetric square root of `s̄` — normalized to sit
   between two concentric adapted ellipsoids, rather than bounded Lipschitz
   domains.  The endpoint constant depends only on the dimension, the regularity
   exponent and the two sandwiching radii, which enter through their ratio.
3. **Skew-centered fluxes.**  The two flux differences, in the Dirichlet estimate
   and in the corrector estimate, subtract the constant skew part of the
   homogenized matrix from the coefficient field, the homogenized matrix entering
   through its symmetric part.
4. **`ℝ≥0∞`-valued norms.**  All norms and energies are valued in `ℝ≥0∞`: the
   integrands are nonnegative, so the Lebesgue integral is defined for every
   argument and is infinite exactly where the reference quantity is, whereas a
   totalized Bochner integral would return zero there and let an estimate be
   satisfied by the failure of the membership it presupposes.
5. **Two ellipticity notions.**  The coefficient carrier is the a.e.-quotient of
   the measurable coefficient fields that are qualitatively locally uniformly
   elliptic, with constants quantified inside the predicate and entering no
   estimate; the quantitative constants `λ` and `Λ` of `e.uniform.ellipticity`
   are the separate hypothesis of the theorem, and every constant in the
   conclusion depends on the dimension and on `Λ/λ` alone.
6. **Positivity of the constants.**  `C`, `C_0` and `C_1` are asserted positive;
   the reference text asserts only their finiteness, and positivity is a
   normalization, every occurrence of each being weakened by increasing it.
7. **Invariance of the event.**  The invariance of `Ω_end` under integer
   translations is carried in the conclusion.

## Running the comparator

```bash
export COMPARATOR_LANDRUN=<landrun v0.1.18>
export COMPARATOR_LEAN4EXPORT=<lean4export built against this project's toolchain>
lake env comparator HCPolyAudit/UniformHomogenization/comparator.json
```

`lean4export` must be the build matching the project's `lean-toolchain`; a
build against a different Lean rejects the produced `.olean` files with
`incompatible header` before any comparison happens.  The acceptance line is
`Your solution is okay!`.
