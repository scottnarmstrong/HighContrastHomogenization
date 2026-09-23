# Correspondence: paper ↔ Lean

This document maps the statement surface of the formalization to the paper
*Homogenization at a polynomial scale in high contrast* (Armstrong, Kuusi,
Loher), so a reader of the paper can locate where each result is proved.

**Conventions.**
- Lean names are given in full; file paths are relative to the repository
  root.
- The **source** column gives the paper's own LaTeX label.
- **Status**: `proved` — formalized and proved as stated; `definition` — a
  definition or predicate rather than a theorem.
- The main results are exposed, stated in full, in
  [`HCPoly/MainResults.lean`](HCPoly/MainResults.lean); each is
  comparator-checked (see [`HCPolyAudit/`](HCPolyAudit/)).
- The modules under [`HCPoly/Consistency/`](HCPoly/Consistency/) check the
  definitions the statements are written with; they are not results of the
  paper and have no rows below.  The one exception is the containment of the
  locally uniformly elliptic coefficient class in the integrability class used
  by the analytic library, which is listed with the standing assumptions.

## Main results

| Source | Lean declaration | File | Status |
|---|---|---|---|
| Theorem A, `t.polynomial.entry` | `HCPoly.polynomial_entry` | `HCPoly/MainResults.lean` | proved |
| Theorem B, `t.algebraic.convergence` | `HCPoly.algebraic_convergence` | `HCPoly/MainResults.lean` | proved |
| Theorem C, `t.uniform.homogenization` | `HCPoly.uniform_homogenization` | `HCPoly/MainResults.lean` | proved |
| Theorem D, `t.random.homogenization` | `HCPoly.polynomial_homogenization` | `HCPoly/MainResults.lean` | proved |
| quenched convergence (used in `ss.random.dirichlet`) | `HCPoly.quenched_convergence` | `HCPoly/MainResults.lean` | proved |

## Standing assumptions

| Source | Lean declaration | File | Status |
|---|---|---|---|
| local uniform ellipticity, `e.qualitative.ellipticity` | `Homogenization.HighContrast.CoeffSpace`, `AEUniformlyEllipticField` | `HCPoly/Setup/CoefficientSpace.lean` | definition |
| local integrability implied by local uniform ellipticity | `Homogenization.HighContrast.isQualitativeEllipticField_of_aeUniformlyEllipticField` | `HCPoly/Consistency/QualitativeClass.lean` | proved |
| ℤ^d-stationarity of the law | `HCPoly.Frozen.IsStationaryLaw` | `HCPoly/Frozen/Stationarity.lean` | definition |
| unit range of dependence | `HCPoly.Frozen.IsUnitRangeLaw` | `HCPoly/Frozen/UnitRange.lean` | definition |
| coarse ellipticity above the source scale, `e.coarse.ellipticity`, with the source tail `e.source.tail` | `HCPoly.Frozen.CoarseEllipticityDagger` | `HCPoly/Frozen/CoarseEllipticityDagger.lean` | definition |
| the coarse block response and the annealed block | `Homogenization.HighContrast.coarseBlock`, `annealedBlock` | `HCPoly/Setup/Response.lean` | definition |
| the reference aspect ratio `e.reference.aspect.ratio` | `Homogenization.HighContrast.aspectRatio` | `HCPoly/Setup/BlockAlgebra.lean` | definition |
| the annealed contrast `e.Theta.m` | `Homogenization.HighContrast.annealedContrast` | `HCPoly/Setup/Response.lean` | definition |
| the assumptions are satisfiable | `Homogenization.HighContrast.exists_law_satisfying_hypotheses` | `HCPoly/Annealed/Witness.lean` | proved |

## The renormalization scheme (Sections 2–5)

These are the statements proved along the route to Theorem A. The scope table
below records any difference from the paper. The first fourteen rows map the
paper's labelled lemmas, propositions and theorem; the next three record
reusable coarse-response inequalities used near `l.source.whitney`.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| scale-selection alternatives, `p.scale.selection` | `Homogenization.HighContrast.scale_selection` | `HCPoly/Entry/Statements/ScaleSelection.lean` | proved |
| standard cubes inside an adapted cube, `l.source.whitney` | `Homogenization.HighContrast.source_whitney` | `HCPoly/Entry/Statements/SourceWhitney.lean` | proved |
| finite-range matrix averaging, `l.fixed.geometry.matrix.averaging` | `Homogenization.HighContrast.fixed_geometry_matrix_averaging` | `HCPoly/Entry/Statements/MatrixAveraging.lean` | proved |
| positive gap, `l.fixed.geometry.positive.gap` | `Homogenization.HighContrast.fixed_geometry_positive_gap` | `HCPoly/Entry/Statements/PositiveGap.lean` | proved |
| parent–child recurrence, `p.fixed.geometry.parent.child.recurrence` | `Homogenization.HighContrast.fixed_geometry_parent_child_recurrence` | `HCPoly/Entry/Statements/ParentChildRecurrence.lean` | proved |
| propagation on one adapted geometry, `p.fixed.geometry.one.grid.propagation` | `Homogenization.HighContrast.fixed_geometry_one_grid_propagation` | `HCPoly/Entry/Statements/OneGridPropagation.lean` | proved |
| Whitney partitions between adapted grids, `l.two.grid.whitney` | `Homogenization.HighContrast.two_grid_whitney` | `HCPoly/Entry/Statements/TwoGridWhitney.lean` | proved |
| the projective step, `l.projective.step` | `Homogenization.HighContrast.projective_step` | `HCPoly/Entry/Statements/ProjectiveStep.lean` | proved |
| comparison after a change of geometry, `p.successful.short.bridge` | `Homogenization.HighContrast.successful_short_bridge` | `HCPoly/Entry/Statements/SuccessfulShortBridge.lean` | proved |
| transport of the complete profile, `p.two.grid.transport` | `Homogenization.HighContrast.two_grid_transport` | `HCPoly/Entry/Statements/TwoGridTransport.lean` | proved |
| Euclidean initialization, `p.initial.fixed.grid.scale` | `Homogenization.HighContrast.initial_fixed_grid_scale` | `HCPoly/Entry/Statements/InitialFixedGridScale.lean` | proved |
| global selection, `p.global.selection` | `Homogenization.HighContrast.global_selection` | `HCPoly/Entry/Statements/GlobalSelection.lean` | proved |
| response and transfer to the Euclidean scale, `p.response.transfer` | `Homogenization.HighContrast.response_transfer` | `HCPoly/Entry/Statements/ResponseTransfer.lean` | proved |
| polynomial entry, `t.polynomial.entry` (the route's root) | `Homogenization.HighContrast.polynomial_entry` | `HCPoly/Entry/Statements/PolynomialEntry.lean` | proved |
| countable subadditivity of the coarse response, used near `l.source.whitney` | `Homogenization.HighContrast.CG.responseJ_subadditive_countable_of_isEllipticFieldOn` | `HCPoly/Entry/CG/Anchors/ResponseSubadditiveCountable.lean` | proved |
| summability of the weighted responses, used near `l.source.whitney` | `Homogenization.HighContrast.CG.summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn` | `HCPoly/Entry/CG/Anchors/ResponseSummable.lean` | proved |
| the finite-family response inequality with its defect, used near `l.source.whitney` | `Homogenization.HighContrast.CG.responseJ_le_sum_volumeRatio_mul_responseJ_add_defect_of_isEllipticFieldOn` | `HCPoly/Entry/CG/Anchors/ResponseFiniteDefect.lean` | proved |
| polynomial entry, `t.polynomial.entry` (the form Theorems B and D consume) | `HCPoly.Frozen.polynomial_entry_random_source` | `HCPoly/Frozen/PolynomialEntry.lean`, proved from the printed form in `HCPoly/Frozen/PolynomialEntryBridge.lean` | proved |

## Section 6: convergence and homogenization

| Source | Lean declaration | File | Status |
|---|---|---|---|
| algebraic convergence, `t.algebraic.convergence` | `Homogenization.HighContrast.Quenched.algebraic_convergence_assembly` | `HCPoly/Provider/Quenched/AlgebraicConvergenceAssembly.lean` | proved |
| quenched convergence of the coarse-grained matrices | `HCPoly.Frozen.quenched_convergence_random_source` | `HCPoly/Frozen/QuenchedConvergence.lean` | proved |
| homogenization with a random source scale, `t.random.homogenization` | `HCPoly.Frozen.polynomial_homogenization_random_source` | `HCPoly/Frozen/PolynomialHomogenization.lean` | proved |
| the uniformly elliptic model, `t.uniform.homogenization` | `Homogenization.HighContrast.uniform_homogenization_of_polynomial_homogenization` | `HCPoly/Provider/UniformEllipticity/UniformHomogenization.lean` | proved |

## Rendering conventions and differences from the printed statements

Every difference is also stated in the docstring of the theorem concerned.

| Where | Paper | Lean |
|---|---|---|
| Theorems A, B, D | `s`, `s⁻¹` and `kᵗ s⁻¹ k` locally essentially bounded (`e.qualitative.ellipticity`) | local uniform ellipticity on each bounded set, modulo a.e. equality; the local ellipticity constants belong to the field and enter no estimate |
| Theorem C | the standing local condition plus the global `(λ, Λ)` bounds of `e.uniform.ellipticity` | the same global bounds are imposed almost surely on the local coefficient space |
| Theorem A | one tolerance `σ ∈ (0,1]`, with `Θ_m ≤ 1 + σ` for every `m ≥ ⌈C log₃(2 + Π K)⌉`; the polynomial length bound follows immediately after the theorem | the same contrast bound; `HCPoly.polynomial_entry` also exports `3^{m_ent} ≤ 3 (2 + Π K)^C` for `m_ent = ⌈C log₃(2 + Π K)⌉` |
| Theorem B | `s̄_* = s̄ > 0`, `k̄ = −k̄ᵗ` | the Schur coefficients of the limit block in the parametrization `e.annealed.schur`: `schurSigmaStar = schurSigma`, `(schurSigma).PosDef`, `IsSkewMat schurSkew` |
| Lemma `l.two.grid.whitney`, `e.two.grid.whitney.counts` | the individual volume-ratio estimate is stated for `r < j − ℓ` | the bound is also proved at `r = j − ℓ`; the printed cardinality bounds keep their respective ranges |
| Theorem C | the `L²` Dirichlet estimate `e.uniform.dirichlet` with a forcing term `f`, and the large-scale energy estimate `e.uniform.energy` | the energy estimate and the instance of Theorem D's homogeneous negative-Sobolev Dirichlet estimate for uniformly elliptic laws (`g = 0`, deterministic source, tail `exp(−t^d)`); the further argument for the paper's forced `L²` form in `ss.uniform.homogenization` is not formalized |
| Theorem C | no corrector, Liouville or first-order approximation clause in its printed statement | the Lean theorem additionally exports these conclusions from the specialization of Theorem D |
| Theorem D | `X ≥ max{1, S}` | `X ≥ 1` |
| Theorem D | the homogenized matrix is the matrix of Theorem B | produced existentially; not identified in the exported statement with the limit block of Theorem B |
| Theorem D, Dirichlet | bounded Lipschitz domains `U ⊆ E₁`; existence and uniqueness of the two solutions; `C₀(U, s, d)` through the size and Lipschitz regularity of the transformed domain `λ̄^{1/2}s̄^{-1/2}U` | normalized adapted cells of the homogenized matrix (translates of `s̄^{1/2}` applied to a triadic cube, between two concentric adapted ellipsoids); supplied weak solutions; `C₀(s, ρ, Rad)` through the radii of two balls trapping the normalized domain |
| Theorem D, fluxes | `(a^ε − k̄)∇u^ε − s̄∇ū` | the same, written for the skew-centered field |
| Theorem D, norms | real-valued norms of the spaces `H^s`, `H^{-s}`, `H^1_s`, `H^1_a` | `ℝ≥0∞`-valued normalized norms `hsNormSq`, `negSobolevNorm`, `negOneNorm`, `weightedGradNorm`; membership classes carry measurability of the function and of its gradient; the weighted classes are closures under globally smooth approximants |
| Theorem D | constants finite | constants positive (a normalization) |
| Theorem D | almost sure statements | one measurable event of full probability, invariant under integer translations, on which every clause holds simultaneously |
