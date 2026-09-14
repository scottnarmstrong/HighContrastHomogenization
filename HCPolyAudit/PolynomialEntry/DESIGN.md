# Comparator surface for `t.polynomial.entry`

`HCPolyAudit/PolynomialEntry/` carries a Mathlib-only comparator challenge for
Theorem A of the high-contrast polynomial-scale paper, and a solution proving
the byte-identical statement from the library.

| File | Role |
| --- | --- |
| `PolynomialEntry/Challenge.lean` | `import Mathlib` only; rebuilds the vocabulary, states the theorem, leaves one `sorry` |
| `PolynomialEntry/SolutionBasic.lean` | verbatim copy of the challenge vocabulary, `import Mathlib` only |
| `Support/PolynomialEntryBridge.lean` | identifies the rebuilt vocabulary with the library objects |
| `PolynomialEntry/Solution.lean` | proves the byte-identical statement |
| `PolynomialEntry/comparator.json` | comparator configuration |
| `check_standalone.sh` | elaborates one file with the project's Lean options |

## The checked statement

```lean
theorem HCPoly.StatementAudit.PolynomialEntry.polynomial_entry
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
        CoarseEllipticityDagger P g E Ψ K S →
        ∃ mEnt : ℕ,
          (mEnt : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
          annealedContrast P (mEnt : ℤ) ≤ 1 + σ ∧
          (3 : ℝ) ^ mEnt ≤ 3 * (2 + aspectRatio E * K) ^ C
```

Every name is the challenge's own definition.

## Definition provenance

| Challenge declaration | Library source |
| --- | --- |
| `Vec`, `Mat`, `BlockVec`, `BlockCoord`, `vecDot`, `vecNormSq`, `matVecMul`, `matTranspose`, `symmPart`, `skewPart`, `blockVecDot`, `blockMatVecMul` | `Homogenization/Ambient/Basic.lean` |
| `BlockMat`, `blockMatEntry`, `blockBasis`, `IsSymmetricBlockMat`, `MatLoewnerLE`, `BlockMatLoewnerLE` | `Homogenization/Ambient/BlockMatrix.lean` |
| `BlockPosDef` | `Homogenization/Book/Ch02/Block.lean` |
| `CoeffField`, `IsEllipticMatrix` | `Homogenization/Ambient/CoefficientField.lean` |
| `AEField`, `intTranslation`, `translateField`, `supDist` | `Homogenization/Probability/Source/AKL.lean` |
| `IsAELocallyUniformlyElliptic`, `AEUniformlyEllipticField`, `CoeffSpace`, `translateCoeff` | `HCPoly/Setup/CoefficientSpace.lean` |
| `IsLocalTest`, `coeffPairing`, `coeffSigma`, `instMeasurableSpaceCoeffSpace`, `UnitSeparated` | `HCPoly/Setup/LocalSigmaFields.lean` |
| `TriadicCube`, `cubeScaleFactor`, `openCubeSet`, `originCube`, `translateCube` | `Homogenization/Geometry/TriadicCube.lean` |
| `centeredCube`, `standardCell`, `standardCellCenter` | `HCPoly/Setup/Geometry.lean` |
| `blockScale`, `IsSkewMat`, `specBound`, `schurSigmaStar`, `schurSkew`, `schurSigma`, `blockContrast`, `lambdaRef`, `bigLambdaRef`, `aspectRatio` | `HCPoly/Setup/BlockAlgebra.lean` |
| `basisVec`, `HasWeakPartialDerivOn`, `HasWeakGradientOn` | `Homogenization/Sobolev/WeakDerivatives.lean` |
| `MemL2On`, `GradMemL2On`, `H1Function`, `H10Function` | `Homogenization/Sobolev/H1/Definitions.lean` |
| `volumeMeasureOn`, `MemVectorL2` | `Homogenization/Sobolev/L2Ambient.lean` |
| `IsPotentialZeroTraceOn`, `IsSolenoidalZeroNormalTraceOn` | `Homogenization/Sobolev/PotentialSolenoidal.lean` |
| `BlockState`, `BlockState.eval`, `blockMatrixOfCoeff`, `blockCoeffField`, `IsBlockMuAdmissible`, `blockEnergyDensity` | `Homogenization/CoarseGraining/BlockFormalism/{Structures,Properties}.lean` |
| `volumeAverage`, `muValueSet`, `Mu`, `coarseBlockEntry`, `coarseBlockMatrix` | `Homogenization/CoarseGraining/Definitions.lean` |
| `coarseBlock`, `annealedBlock`, `annealedContrast` | `HCPoly/Setup/Response.lean` |
| `upperTailEvent`, `AdmissiblePsi` | `Homogenization/Probability/IndependentSums/WeakOrlicz.lean` |
| `HasPsiGrowth` | `Homogenization/Probability/IndependentSums/PsiCalculus.lean` |
| `IsStationaryLaw`, `IsUnitRangeLaw`, `CoarseEllipticityDagger` | `HCPoly/Frozen/{Stationarity,UnitRange,CoarseEllipticityDagger}.lean` |

The challenge carries no declaration outside this table: a dependency walk of
the theorem's statement closure reaches every one of them, and nothing else.

## Bridge inventory

**Definitionally shared.**  The following rebuilt objects unfold to the library
objects, so the identification is `rfl` (checked in the bridge file, or used
silently where the two terms are interchangeable):

* the carrier `CoeffSpace d`, since `Vec`, `Mat` and the a.e.-quotient are
  Mathlib types and every predicate in the subtype is a chain of plain `def`s
  with identical bodies;
* `translateField`, `translateCoeff` (the ellipticity side condition is a
  proof, hence definitionally irrelevant), `supDist`, `UnitSeparated`;
* `coeffPairing`, hence the generating statistics of the local σ-fields;
* `centeredCube`, `standardCell`, `standardCellCenter`: the cube records are
  structure literals, so their projections reduce;
* the Schur data, `blockContrast`, `lambdaRef`, `bigLambdaRef`, `aspectRatio`,
  `blockScale`, `BlockMatLoewnerLE`, `IsSymmetricBlockMat`, `BlockPosDef`,
  read through the block-matrix conversion;
* `blockEnergyDensity` and `volumeAverage`, read through the state conversion;
* `AdmissiblePsi`, `HasPsiGrowth`, `upperTailEvent`.

**Structure copies.**  `BlockMat`, `BlockState`, `H1Function`, `H10Function`
and `TriadicCube` are inductive types, so the rebuilt copies are new types.
Each field of each copy has a type definitionally equal to the corresponding
library field, so both conversion directions are single constructor
applications (`toRepoBlock`/`ofRepoBlock`, `toRepoState`/`ofRepoState`,
`toRepoH1`/`ofRepoH1`, `toRepoH10`/`ofRepoH10`).  `TriadicCube` never needs a
conversion: it is consumed only through `openCubeSet` of a structure literal.

**The variational quantity.**  `IsBlockMuAdmissible` quantifies over `H¹₀`
witnesses existentially (in `IsPotentialZeroTraceOn`) and over `H¹` witnesses
universally (in `IsSolenoidalZeroNormalTraceOn`), so both conversion directions
are used.  With those, the two `muValueSet`s are the same set of reals and the
two `Mu`s the same infimum; polarization then identifies the coarse block
responses entrywise through `blockMatEntry_coarseBlockMatrix`.

**The measurable structure.**  The test class `IsLocalTest` is a
one-constructor record, so the two generating families of the local σ-fields are
equal only propositionally.  The resulting equality
`coeffSigma d U = Homogenization.HighContrast.coeffSigma d U`, at `U = univ`,
is an equality of the two `MeasurableSpace (CoeffSpace d)` instances; laws are
transported along it by `castMeasure`, and the transport commutes with
`Measure.map`, `Measure.real`, the Bochner integral, the almost-everywhere
filter, `IsProbabilityMeasure`, `Measurable`, and `ProbabilityTheory.Indep`.
These are all proved by substituting the instance equality.

## Presentation deltas

1. **One tolerance instead of a calibration triple.**  The library statement
   quantifies a triple `(c_sc, δ₀, c_end)` with
   `(1 + δ₀)² (1 + c_end) ≤ 1 + c_sc` and produces
   `c_* ∈ (0, min c_sc c_end]` with `Θ_{m_ent} - 1 ≤ c_*`, the tolerance being
   chosen before the coarse-ellipticity exponent.  The challenge takes the
   printed form: a single `σ ∈ (0, 1]`, with the conclusion
   `Θ_{m_ent} ≤ 1 + σ` of `e.polynomial.entry`.  The solution instantiates the
   triple at `(σ, σ/8, σ/8)`, which is admissible because `(1 + σ/8)³ ≤ 1 + σ`
   for `0 < σ ≤ 1`, and then `c_* ≤ min σ (σ/8) ≤ σ`.  The challenge is
   therefore the printed statement and is implied by the library one; it does
   not assert the library's finer calibration bookkeeping.
2. **Aspect ratio and contrast in Loewner-scaling form.**  `Π` and `Θ_m` are
   presented as infima of the scalars `t ≥ 0` realizing a Loewner bound, which
   is how the library encodes the printed matrix norms
   `e.reference.aspect.ratio` and `e.Theta.m`.
3. **The coefficient class.**  The carrier is the a.e.-quotient of the
   measurable coefficient fields that are qualitatively locally uniformly
   elliptic; the ellipticity constants are quantified inside the predicate and
   enter no estimate, exactly as in the library.

## Running the comparator

```bash
export COMPARATOR_LANDRUN=/usr/local/bin/landrun
export COMPARATOR_LEAN4EXPORT=<lean4export built against this project's toolchain>
lake env comparator HCPolyAudit/PolynomialEntry/comparator.json
```

`lean4export` must be the build matching the project's `lean-toolchain`; a
build against a different Lean rejects the produced `.olean` files with
`incompatible header` before any comparison happens.  The acceptance line is
`Your solution is okay!`.
