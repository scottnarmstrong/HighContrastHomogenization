# Comparator surface for `t.random.homogenization`

`HCPolyAudit/PolynomialHomogenization/` carries a Mathlib-only comparator challenge
for Theorem D of the high-contrast polynomial-scale paper, and a solution
proving the byte-identical statement from the library.

| File | Role |
| --- | --- |
| `PolynomialHomogenization/Challenge.lean` | `import Mathlib` only; rebuilds the vocabulary, states the theorem, leaves one `sorry` |
| `PolynomialHomogenization/SolutionBasic.lean` | verbatim copy of the challenge vocabulary, `import Mathlib` only |
| `Support/PolynomialHomogenizationBridge1.lean` | the algebraic, geometric and Sobolev bridges, and the transport of a law |
| `Support/PolynomialHomogenizationBridge2.lean` | the analytic bridges and the three standing hypotheses |
| `PolynomialHomogenization/Solution.lean` | proves the byte-identical statement |
| `PolynomialHomogenization/comparator.json` | comparator configuration |
| `check_standalone.sh` | elaborates one file with the project's Lean options |

## The checked statement

```lean
theorem HCPoly.StatementAudit.PolynomialHomogenization.polynomial_homogenization
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (cd : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ), 0 < cd ∧
      (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ (C cSrc κ : ℝ) (C₁ : ℝ → ℝ),
          0 < C ∧ 0 < cSrc ∧ 0 < κ ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ)
            (K : ℝ) (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
            CoarseEllipticityDagger P g E Ψ K S →
            ∃ (abar : Mat d) (Lpoly : ℝ) (X : CoeffSpace d → ℝ)
              (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
              (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
              1 ≤ Lpoly ∧ Measurable X ∧ (∀ a, 1 ≤ X a) ∧
              -- linearity in the slope and stationarity of the corrector family
              … ∧
              -- the polynomial length and the tail `e.random.scale.tail`
              Lpoly ≤ (2 + aspectRatio E * K) ^ C ∧
              (∀ t : ℝ, 1 ≤ t →
                P.real {a | C * Lpoly * t ≤ X a} ≤
                  Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) + (Ψ (cSrc * t))⁻¹) ∧
              (∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
              ∃ Ωend : Set (CoeffSpace d),
                MeasurableSet Ωend ∧ P.real Ωend = 1 ∧
                (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
                -- `e.random.dirichlet`, `e.random.corrector`,
                -- `e.random.liouville.growth`, `e.random.energy` and
                -- `e.random.regularity`
                …
```

Every name is the challenge's own definition; the elided clauses are written out
in full in `Challenge.lean`.

## Definition provenance

| Challenge declaration | Library source |
| --- | --- |
| `Vec`, `Mat`, `BlockVec`, `BlockCoord`, `vecDot`, `vecNormSq`, `matVecMul`, `matTranspose`, `blockVecDot`, `blockMatVecMul`, `symmPart`, `skewPart` | `Homogenization/Ambient/Basic.lean` |
| `BlockMat`, `blockMatEntry`, `blockBasis`, `IsSymmetricBlockMat`, `MatLoewnerLE`, `BlockMatLoewnerLE` | `Homogenization/Ambient/BlockMatrix.lean` |
| `BlockPosDef` | `Homogenization/Book/Ch02/Block.lean` |
| `CoeffField`, `IsEllipticMatrix` | `Homogenization/Ambient/CoefficientField.lean` |
| `AEField`, `intTranslation`, `translateField`, `supDist` | `Homogenization/Probability/Source/AKL.lean` |
| `IsAELocallyUniformlyElliptic`, `AEUniformlyEllipticField`, `CoeffSpace`, `translateCoeff` | `HCPoly/Setup/CoefficientSpace.lean` |
| `IsLocalTest`, `coeffPairing`, `coeffSigma`, `instMeasurableSpaceCoeffSpace`, `UnitSeparated` | `HCPoly/Setup/LocalSigmaFields.lean` |
| `TriadicCube`, `cubeScaleFactor`, `openCubeSet`, `originCube`, `translateCube` | `Homogenization/Geometry/TriadicCube.lean` |
| `centeredCube`, `standardCell`, `standardCellCenter`, `matImage`, `HasBallSandwich`, `ellipsoid` | `HCPoly/Setup/Geometry.lean` |
| `basisVec`, `HasWeakPartialDerivOn`, `HasWeakGradientOn` | `Homogenization/Sobolev/WeakDerivatives.lean` |
| `MemL2On`, `GradMemL2On`, `H1Function`, `H10Function` | `Homogenization/Sobolev/H1/Definitions.lean` |
| `volumeMeasureOn`, `MemVectorL2` | `Homogenization/Sobolev/L2Ambient.lean` |
| `IsPotentialZeroTraceOn`, `IsSolenoidalZeroNormalTraceOn` | `Homogenization/Sobolev/PotentialSolenoidal.lean` |
| `BlockState`, `BlockState.eval`, `blockMatrixOfCoeff`, `blockCoeffField`, `IsBlockMuAdmissible`, `blockEnergyDensity` | `Homogenization/CoarseGraining/BlockFormalism/{Structures,Properties}.lean` |
| `volumeAverage`, `muValueSet`, `Mu`, `coarseBlockEntry`, `coarseBlockMatrix` | `Homogenization/CoarseGraining/Definitions.lean` |
| `coarseBlock` | `HCPoly/Setup/Response.lean` |
| `blockScale`, `IsSkewMat`, `specBound`, `schurSkew`, `schurSigma`, `lambdaRef`, `bigLambdaRef`, `aspectRatio`, `matSqrt` | `HCPoly/Setup/BlockAlgebra.lean` |
| `upperTailEvent`, `AdmissiblePsi` | `Homogenization/Probability/IndependentSums/WeakOrlicz.lean` |
| `HasPsiGrowth` | `Homogenization/Probability/IndependentSums/PsiCalculus.lean` |
| `scaledCoeff`, `euclideanBallAt`, `euclideanBall`, `smoothGrad`, `IsLocalVecTest`, `eVolumeAverage`, `normalizedL2Norm`, `weightedGradNorm`, `fracSeminormSq`, `hsNormSq`, `h1NormSq`, `dualPairing`, `negSobolevNorm`, `negOneNorm`, `sEnergyOn`, `h1sNormSqOn`, `skewFluxPairing`, `skewFluxDualNorm`, `IsMeasurableGradientPair`, `MemH1a`, `MemH1a0`, `MemH1sLoc`, `IsWeakSolutionOn`, `MemLiouvilleClass`, `MemAffineH10` | `HCPoly/Setup/AnalyticCarriers.lean` |
| `IsStationaryLaw`, `IsUnitRangeLaw`, `CoarseEllipticityDagger` | `HCPoly/Frozen/{Stationarity,UnitRange,CoarseEllipticityDagger}.lean` |

The challenge carries no declaration outside this table: a dependency walk of
the theorem's statement closure reaches every one of them, and nothing else.

## Bridge inventory

**Definitionally shared.**  The following rebuilt objects unfold to the library
objects, so the identification is `rfl` (checked in a bridge file, or used
silently where the two terms are interchangeable):

* the carrier `CoeffSpace d`, since `Vec`, `Mat` and the a.e.-quotient are
  Mathlib types and every predicate in the subtype is a chain of plain `def`s
  with identical bodies;
* `translateField`, `translateCoeff` (the ellipticity side condition is a
  proof, hence definitionally irrelevant), `intTranslation`, `supDist`,
  `UnitSeparated`;
* `coeffPairing`, hence the generating statistics of the local σ-fields;
* `centeredCube`, `standardCell`, `standardCellCenter` and
  `openCubeSet (originCube d j)`: the cube records are structure literals, so
  their projections reduce;
* the Schur data, `lambdaRef`, `bigLambdaRef`, `aspectRatio`, `blockScale`,
  `specBound`, `matSqrt`, `BlockMatLoewnerLE`, `IsSymmetricBlockMat`,
  `BlockPosDef`, read through the block-matrix conversion;
* `blockEnergyDensity` and `volumeAverage`, read through the state conversion;
* `AdmissiblePsi`, `HasPsiGrowth`, `upperTailEvent`;
* `scaledCoeff`, `eVolumeAverage`, `normalizedL2Norm`, `weightedGradNorm`,
  `fracSeminormSq`, `hsNormSq`, `h1NormSq`, `dualPairing`, `sEnergyOn`,
  `h1sNormSqOn`, `skewFluxPairing`, `matImage`, `HasBallSandwich`, `ellipsoid`,
  `euclideanBallAt`, `euclideanBall`, `smoothGrad`;
* `HasWeakPartialDerivOn`, `HasWeakGradientOn`, `MemL2On`, `GradMemL2On`,
  `IsMeasurableGradientPair`, `MemH1sLoc`.

**Structure copies.**  `BlockMat`, `BlockState`, `H1Function`, `H10Function`
and `TriadicCube` are inductive types, so the rebuilt copies are new types.
Each field of each copy has a type definitionally equal to the corresponding
library field, so both conversion directions are single constructor
applications (`toBlk`, `toRepoBlockState`/`ofRepoBlockState`,
`toRepoH1`/`ofRepoH1`, `toRepoH10`/`ofRepoH10`).  `TriadicCube` never needs a
conversion: it is consumed only through `openCubeSet` of a structure literal.

**The variational quantity.**  `IsBlockMuAdmissible` quantifies over `H¹₀`
witnesses existentially (in `IsPotentialZeroTraceOn`) and over `H¹` witnesses
universally (in `IsSolenoidalZeroNormalTraceOn`), so both conversion directions
are used.  With those, the two `muValueSet`s are the same set of reals and the
two `Mu`s the same infimum; polarization then identifies the coarse block
responses entrywise through `toBlk_coarseBlockMatrix`.

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
and the transport commutes with `Measure.map`, `Measure.real`, the Bochner
integral, the almost-everywhere filter, `IsProbabilityMeasure`, `Measurable`,
`MeasurableSet` and `ProbabilityTheory.Indep`.  These are all proved by
substituting the instance equality.  The three standing hypotheses on the law
travel with it (`isStationaryLaw_toRepoLaw`, `isUnitRangeLaw_toRepoLaw`,
`coarseEllipticityDagger_toRepoLaw`).

## Presentation deltas

1. **Structure copies.**  `BlockMat`, `TriadicCube`, `BlockState`,
   `H1Function`, `H10Function`, `IsLocalTest`, `IsLocalVecTest` and
   `CoarseEllipticityDagger` are inductive copies of the corresponding library
   structures.  Every field has the same name and a type that unfolds to the
   library one, so the two readings differ by a field shuffle and nothing else.
2. **The quotient carrier.**  The almost-everywhere quotient carrier is written
   as the Mathlib quotient `Vec d →ₘ[volume] Mat d`; this is the library's own
   carrier, written without its abbreviation.  Its elements are qualitatively
   locally uniformly elliptic, with ellipticity constants belonging to the field
   and to the ball and entering no estimate.
3. **The polarization entry.**  `coarseBlockEntry` is a public copy of a library
   declaration that is private there; the body is the same.
4. **The square root.**  `matSqrt` is copied with the same choice-based
   definition; it is the unique positive semidefinite square root on positive
   semidefinite data, which is what pins it.
5. **The standing hypotheses.**  The three standing hypotheses on the law are
   written as free-standing declarations rather than through the library's names
   for them; the bodies agree.
6. **The measurable structure.**  Because the generators of the local `σ`-fields
   mention the test-function record of delta 1, the measurable structure of the
   coefficient space agrees with the library's as a value rather than by
   unfolding, and a law is read across that identification.  The two `σ`-fields
   have the same generating sets, so the identification is an equality of
   measurable structures and nothing about the law changes under it.
7. **Adapted domains.**  The domains carrying the Dirichlet estimate are the
   adapted cells of the homogenized matrix — translates of the image of a centred
   triadic cube under the symmetric square root of `s̄` — normalized to sit
   between two concentric adapted ellipsoids, rather than bounded Lipschitz
   domains.  The shape constant depends only on the dimension, the regularity
   exponent and the two sandwiching radii, which enter through their ratio.
8. **Skew-centered fluxes.**  The two flux differences, in the Dirichlet estimate
   and in the corrector estimate, subtract the constant skew part of the
   homogenized matrix from the coefficient field, the homogenized matrix entering
   through its symmetric part.
9. **`ℝ≥0∞`-valued norms.**  All norms and energies are valued in `ℝ≥0∞`: the
   integrands are nonnegative, so the Lebesgue integral is defined for every
   argument and is infinite exactly where the reference quantity is, whereas a
   totalized Bochner integral would return zero there and let an estimate be
   satisfied by the failure of the membership it presupposes.  The three
   membership classes carry the measurability of the function and of its gradient
   field that their printed counterparts presuppose, and the
   coefficient-weighted spaces are closures under globally smooth approximants.
10. **Positivity of the constants.**  `C`, `C_0` and `C_1` are asserted positive;
    the reference text asserts only their finiteness, and positivity is a
    normalization, every occurrence of each being weakened by increasing it.
11. **Invariance of the event.**  The invariance of `Ω_end` under integer
    translations is carried in the conclusion.

## Running the comparator

```bash
export COMPARATOR_LANDRUN=<landrun v0.1.18>
export COMPARATOR_LEAN4EXPORT=<lean4export built against this project's toolchain>
lake env comparator HCPolyAudit/PolynomialHomogenization/comparator.json
```

`lean4export` must be the build matching the project's `lean-toolchain`; a
build against a different Lean rejects the produced `.olean` files with
`incompatible header` before any comparison happens.  The acceptance line is
`Your solution is okay!`.
