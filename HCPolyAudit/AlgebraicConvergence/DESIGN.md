# Comparator surface for `t.algebraic.convergence`

`HCPolyAudit/AlgebraicConvergence/` carries a Mathlib-only comparator challenge for
Theorem B of the high-contrast polynomial-scale paper, and a solution proving
the byte-identical statement from the library.

| File | Role |
| --- | --- |
| `AlgebraicConvergence/Challenge.lean` | `import Mathlib` only; rebuilds the vocabulary, states the theorem, leaves one `sorry` |
| `AlgebraicConvergence/SolutionBasic.lean` | verbatim copy of the challenge vocabulary, `import Mathlib` only |
| `Support/AlgebraicConvergenceBridge.lean` | identifies the rebuilt vocabulary with the library objects |
| `AlgebraicConvergence/Solution.lean` | proves the byte-identical statement |
| `AlgebraicConvergence/comparator.json` | comparator configuration |
| `check_standalone.sh` | elaborates one file with the project's Lean options |

## The checked statement

```lean
theorem HCPoly.StatementAudit.AlgebraicConvergence.algebraic_convergence
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
        CoarseEllipticityDagger P g E Ψ K S →
        ∃ (m₀ : ℕ) (Abar : BlockMat d),
          (m₀ : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
          (∀ j : ℕ,
            annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
              (3 : ℝ) ^ (-κ * (j : ℝ))) ∧
          IsSymmetricBlockMat Abar ∧
          BlockPosDef Abar ∧
          (∀ j : ℕ,
            BlockMatLoewnerLE Abar
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ))) ∧
            BlockMatLoewnerLE
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ)))
              (blockScale (1 + 6 * (3 : ℝ) ^ (-κ * (j : ℝ))) Abar)) ∧
          schurSigmaStar Abar = schurSigma Abar ∧
          (schurSigma Abar).PosDef ∧
          IsSkewMat (schurSkew Abar)
```

Every name except `Matrix.PosDef` is the challenge's own definition.

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

Positive definiteness of the Schur symmetric block is Mathlib's own
`Matrix.PosDef`, at the shared carrier `Matrix (Fin d) (Fin d) ℝ`.

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
* `IsSkewMat`, which is a predicate on the shared matrix carrier;
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

**The block-matrix conversion in both directions.**  The hypotheses of the
theorem name a reference block, so `toRepoBlock` carries `IsSymmetricBlockMat`,
`BlockPosDef`, `BlockMatLoewnerLE`, `blockScale` and `aspectRatio` into the
library.  The conclusions name a limit block, so `ofRepoBlock` carries
`IsSymmetricBlockMat`, `BlockPosDef`, `BlockMatLoewnerLE`, `blockScale` and the
three Schur blocks back out; the annealed block of a centred cube is identified
in the same converted form.  Every one of these is a field shuffle over the four
shared blocks.

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

1. **The block convergence without block subtraction.**  The printed display
   `e.algebraic.block.decay` is `0 ≤ 𝐀̄(□_{m₀+j}) - 𝐀̄ ≤ 6 · 3^{-κ j} 𝐀̄`.  The
   challenge states the equivalent pair of Loewner bounds
   `𝐀̄ ≤ 𝐀̄(□_{m₀+j})` and `𝐀̄(□_{m₀+j}) ≤ (1 + 6 · 3^{-κ j}) 𝐀̄`, using the
   scalar dilation `blockScale` instead of a difference of doubled blocks.
2. **The limit block in four-block form.**  The limit is a `BlockMat d`, so its
   symmetry and positive definiteness are the entrywise `IsSymmetricBlockMat`
   and the doubled quadratic form `BlockPosDef`, not the corresponding
   properties of a `2d × 2d` matrix.  The Schur conclusion `s̄_* = s̄ > 0`,
   `k̄ = -k̄ᵗ` is read off by `schurSigmaStar`, `schurSigma` and `schurSkew`
   in the parametrization `e.annealed.schur`, the positivity of `s̄` being
   Mathlib's `Matrix.PosDef`.
3. **Aspect ratio and contrast in Loewner-scaling form.**  `Π` and `Θ_m` are
   presented as infima of the scalars `t ≥ 0` realizing a Loewner bound, which
   is how the library encodes the printed matrix norms
   `e.reference.aspect.ratio` and `e.Theta.m`.
4. **The reference block.**  It is an arbitrary symmetric positive definite
   doubled block matrix rather than a matrix presented in the Schur form
   `e.reference.block`; its Schur data `σ₀`, `κ₀`, `σ_{*,0}` are read off from
   it.
5. **The coefficient class.**  The carrier is the a.e.-quotient of the
   measurable coefficient fields that are qualitatively locally uniformly
   elliptic; the ellipticity constants are quantified inside the predicate and
   enter no estimate, exactly as in the library.
6. **Indexing.**  The generation is a natural number `m₀` and the scales
   `m₀ + j` are read as integers, the centred cube `□_m` being defined at every
   integer scale.

## Running the comparator

```bash
export COMPARATOR_LANDRUN=<landrun binary>
export COMPARATOR_LEAN4EXPORT=<lean4export built against this project's toolchain>
lake env comparator HCPolyAudit/AlgebraicConvergence/comparator.json
```

`lean4export` must be the build matching the project's `lean-toolchain`; a
build against a different Lean rejects the produced `.olean` files with
`incompatible header` before any comparison happens.  Delete the build
artifacts of `HCPolyAudit/AlgebraicConvergence` before the run, so that the challenge
and the solution are both rebuilt under the comparator.  The acceptance line is
`Your solution is okay!`.
