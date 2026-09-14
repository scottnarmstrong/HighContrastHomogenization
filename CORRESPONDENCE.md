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
| coefficient fields and the qualitative class, `e.qualitative.ellipticity` | `Homogenization.HighContrast.CoeffSpace`, `AEUniformlyEllipticField` | `HCPoly/Setup/CoefficientSpace.lean` | definition |
| containment of the formalized class in the qualitative class | `Homogenization.HighContrast.isQualitativeEllipticField_of_aeUniformlyEllipticField` | `HCPoly/Setup/QualitativeClass.lean` | proved |
| ℤ^d-stationarity of the law | `HCPoly.Frozen.IsStationaryLaw` | `HCPoly/Frozen/Stationarity.lean` | definition |
| unit range of dependence | `HCPoly.Frozen.IsUnitRangeLaw` | `HCPoly/Frozen/UnitRange.lean` | definition |
| coarse ellipticity above the source scale, `e.coarse.ellipticity`, with the source tail `e.source.tail` | `HCPoly.Frozen.CoarseEllipticityDagger` | `HCPoly/Frozen/CoarseEllipticityDagger.lean` | definition |
| the coarse block response and the annealed block | `Homogenization.HighContrast.coarseBlock`, `annealedBlock` | `HCPoly/Setup/Response.lean` | definition |
| the reference aspect ratio `e.reference.aspect.ratio` | `Homogenization.HighContrast.aspectRatio` | `HCPoly/Setup/BlockAlgebra.lean` | definition |
| the annealed contrast `e.Theta.m` | `Homogenization.HighContrast.annealedContrast` | `HCPoly/Setup/Response.lean` | definition |
| the assumptions are satisfiable | `Homogenization.HighContrast.exists_law_satisfying_hypotheses` | `HCPoly/Annealed/Witness.lean` | proved |

## The renormalization scheme (Sections 2–5)

The certified statement surface below Theorem A. Each declaration is the
exact statement the proof of the corresponding paper result establishes;
where the paper folds several of them into one proposition, the row says so.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| the source multiplier on a window, `e.source.multiplier` | `HCPoly.Frozen.random_source_window` | `HCPoly/Frozen/RandomSourceWindow.lean` | proved |
| the source estimate on adapted cubes, `e.source.adapted.bound` | `HCPoly.Frozen.random_source_control` | `HCPoly/Frozen/RandomSourceControl.lean` | proved |
| the parent–child recurrence, `p.fixed.geometry.parent.child.recurrence` | `HCPoly.Frozen.fixed_grid_recurrence` | `HCPoly/Frozen/FixedGridRecurrence.lean` | proved |
| propagation on one adapted geometry, `p.fixed.geometry.one.grid.propagation` | `HCPoly.Frozen.portable_history` | `HCPoly/Frozen/PortableHistory.lean` | proved |
| comparison after a change of geometry, `p.successful.short.bridge` (the short bridge) | `HCPoly.Frozen.random_source_bridge_short_hop` | `HCPoly/Frozen/RandomSourceBridgeShortHop.lean` | proved |
| comparison after a change of geometry, `p.successful.short.bridge` (the two-grid shifted drift) | `HCPoly.Frozen.random_source_bridge_two_grid_shifted_drift` | `HCPoly/Frozen/RandomSourceBridgeTwoGridShiftedDrift.lean` | proved |
| transport of the complete profile, `p.two.grid.transport` | `HCPoly.Frozen.random_source_grid_transport` | `HCPoly/Frozen/RandomSourceGridTransport.lean` | proved |
| Euclidean initialization, `p.initial.fixed.grid.scale` | `HCPoly.Frozen.random_source_adapted_initialization` | `HCPoly/Frozen/RandomSourceAdaptedInitialization.lean` | proved |
| global selection, `p.global.selection` | `HCPoly.Frozen.random_source_global_selection` | `HCPoly/Frozen/RandomSourceGlobalSelection.lean` | proved |
| the adapted response estimate, `e.response.adapted.conclusion` (part of `p.response.transfer`) | `HCPoly.Frozen.random_adapted_response` | `HCPoly/Frozen/RandomAdaptedResponse.lean` | proved |
| persistence and Euclidean transfer, `p.response.transfer` | `HCPoly.Frozen.random_persistence_transfer` | `HCPoly/Frozen/RandomPersistenceTransfer.lean` | proved |
| polynomial entry, `t.polynomial.entry` (calibration-triple form) | `HCPoly.Frozen.polynomial_entry_random_source` | `HCPoly/Frozen/PolynomialEntry.lean` | proved |

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
| all theorems | coefficient fields satisfying the qualitative condition `e.qualitative.ellipticity` | fields locally uniformly elliptic almost everywhere, modulo a.e. equality; the ellipticity constants belong to the field and enter no estimate; the containment in the qualitative class is proved |
| Theorem A | one tolerance `σ ∈ (0,1]` | the same; the certified statement `polynomial_entry_random_source` carries a calibration triple, and the paper's form is derived from it |
| Theorem B | `s̄_* = s̄ > 0`, `k̄ = −k̄ᵗ` | the Schur coefficients of the limit block in the parametrization `e.annealed.schur`: `schurSigmaStar = schurSigma`, `(schurSigma).PosDef`, `IsSkewMat schurSkew` |
| Theorem C | the `L²` Dirichlet estimate `e.uniform.dirichlet` with a forcing term `f` | the instance of Theorem D for uniformly elliptic laws (`g = 0`, deterministic source, tail `exp(−t^d)`); the Dirichlet clause is Theorem D's homogeneous negative-Sobolev estimate. The paper's forced `L²` form is deduced in `ss.uniform.homogenization` by a further duality argument, which is not formalized |
| Theorem D | `X ≥ max{1, S}` | `X ≥ 1` |
| Theorem D | the homogenized matrix is the matrix of Theorem B | produced existentially; not identified in the exported statement with the limit block of Theorem B |
| Theorem D, Dirichlet | bounded Lipschitz domains `U ⊆ E₁`; existence and uniqueness of the two solutions; `C₀(U, s, d)` through the Lipschitz character | normalized adapted cells of the homogenized matrix (translates of `s̄^{1/2}` applied to a triadic cube, between two concentric adapted ellipsoids); supplied weak solutions; `C₀(s, ρ, Rad)` through the radii of two balls trapping the normalized domain |
| Theorem D, fluxes | `(a^ε − k̄)∇u^ε − s̄∇ū` | the same, written for the skew-centered field |
| Theorem D, norms | real-valued norms of the spaces `H^s`, `H^{-s}`, `H^1_s`, `H^1_a` | `ℝ≥0∞`-valued normalized norms `hsNormSq`, `negSobolevNorm`, `negOneNorm`, `weightedGradNorm`; membership classes carry measurability of the function and of its gradient; the weighted classes are closures under globally smooth approximants |
| Theorem D | constants finite | constants positive (a normalization) |
| Theorem D | almost sure statements | one measurable event of full probability, invariant under integer translations, on which every clause holds simultaneously |
