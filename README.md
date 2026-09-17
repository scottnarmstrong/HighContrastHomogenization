# HighContrastHomogenization

A machine-checked **Lean 4** formalization of the paper
*Homogenization at a polynomial scale in high contrast*
(Scott Armstrong, Tuomo Kuusi, and Amélie Loher; arXiv identifier to be
added on posting).  It is built on
[`mathlib`](https://github.com/leanprover-community/mathlib4) and imports
the public
[`CoarseGraining`](https://github.com/scottnarmstrong/CoarseGraining)
homogenization library — a 600k+-line formalization by the first two authors —
as its analytic base.

[![CI](https://github.com/scottnarmstrong/HighContrastHomogenization/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/HighContrastHomogenization/actions/workflows/build.yml)
[![Comparator audit](https://github.com/scottnarmstrong/HighContrastHomogenization/actions/workflows/comparator.yml/badge.svg)](https://github.com/scottnarmstrong/HighContrastHomogenization/actions/workflows/comparator.yml)

## What this is

The paper studies divergence-form elliptic equations with stationary,
possibly nonsymmetric coefficients satisfying a *coarse ellipticity*
condition above a random source scale: the coarse-grained coefficient
blocks are dominated by a fixed reference block with a discount factor
`3^{γ(m-k)}`, `γ ∈ [0,1)`, once the microscopic source scale has been
passed.  Under unit range of dependence, it proves that the coefficients
enter the small-contrast regime at a length **polynomial** in the reference
aspect ratio `Π` and the source-tail growth constant `K`, where the earlier
high-contrast theory gave a quasipolynomial length.  Combining this with the
high-contrast homogenization theory of Armstrong and Kuusi (*Renormalization
Group and Elliptic Homogenization in High Contrast*, Invent. Math. 2025)
gives algebraic convergence of the annealed coarse-grained matrices,
quantitative Dirichlet homogenization, corrector estimates, a first-order
Liouville theorem, and large-scale regularity above a single random radius
whose tail has a stretched-exponential term and a rescaled copy of the
source-tail bound.

This repository formalizes that paper.  The renormalization scheme of the
paper's Sections 2–5 — the source Whitney decomposition and scale selection,
matrix averaging and the positive gap, the parent–child recurrence and
propagation on one adapted grid, the two-grid Whitney construction, the
projective step, the successful short bridge and two-grid transport, the
Euclidean initialization, global selection and response transfer — is
formalized in full, each step carried by a named theorem stating the
proposition of the paper it proves, and so are the deductions of Section 6
that the theorems below state.

All four theorems of the paper's introduction — Theorems A, B, C and D — are
formalized and proved, each exported in the paper's own form in
`HCPoly/MainResults.lean` and each checked against a Mathlib-only
restatement by the Lean comparator.  Theorem C is obtained as the instance
of Theorem D for uniformly elliptic laws; its Dirichlet clause is exported
in the negative-Sobolev form of Theorem D rather than the paper's `L²`
form with a forcing term, as explained below.

- **1,973 Lean source files, 406,339 lines** (including the comparator
  audit surface; the library itself is 1,956 files and 399,057 lines).
- **No `sorry`** anywhere in the library.  (Each Mathlib-only comparator
  challenge in `HCPolyAudit/` contains its single intentional statement-level
  `sorry`, filled by the corresponding solution file.)
- **No custom `axiom`.**  The main theorems reduce to `mathlib`'s three
  standard foundational axioms — `propext`, `Classical.choice`, `Quot.sound` —
  verified by
  [`HCPoly/Meta/AxiomsAudit.lean`](HCPoly/Meta/AxiomsAudit.lean).
- Pinned to Lean `v4.33.0`, `mathlib` `v4.33.0`, and `CoarseGraining` at a
  fixed revision.

## What changed in this release

Theorem A is now proved along the paper's own route.  Each step of Sections 2–5
— the source Whitney decomposition, scale selection, matrix averaging and the
positive gap, the parent–child recurrence, propagation on one adapted grid, the
two-grid Whitney construction, the projective step, the successful short bridge,
two-grid transport, the Euclidean initialization, global selection and response
transfer — is a named theorem under `HCPoly/Entry/Statements/`, and Theorem A is
assembled from them.  The exported statement is the printed one: the annealed
contrast is at most `1 + σ` at *every* generation beyond the entry scale, where
the previous release asserted it at one generation only.

The previous proof of Theorem A and the 212 modules that served it alone have
been removed.  Theorems B, C and D, their proofs and their comparator pairs are
unchanged, and so are the toolchain (Lean `v4.33.0`, `mathlib` `v4.33.0`) and
the dependency pins.  The comparator pair for Theorem A was restated in the new
printed form and re-proved.

## Main results

The headline theorems are stated in full in
[`HCPoly/MainResults.lean`](HCPoly/MainResults.lean), each proved by direct
application to its certified counterpart, so the statements displayed there
are faithful to the verified ones.

* **`HCPoly.polynomial_entry`** (Theorem A of the paper) — polynomial entry
  into small contrast: for every tolerance `σ ∈ (0,1]` there is a constant
  `C(σ, d, γ)`, independent of the reference block, of the law, of the
  reference aspect ratio `Π` and of the source-tail growth constant `K`, such
  that, for every law satisfying the standing assumptions, the annealed
  contrast `Θ_m` is at most `1 + σ` at **every** generation
  `m ≥ ⌈C log₃(2 + Π K)⌉`; and the entry generation
  `m_ent = ⌈C log₃(2 + Π K)⌉` has length `3^{m_ent} ≤ 3 (2 + Π K)^C`,
  polynomial in `Π` and `K`.
* **`HCPoly.algebraic_convergence`** (Theorem B) — algebraic convergence at a
  polynomial scale: beyond a generation `m₀ ≤ ⌈C log₃(2 + Π K)⌉` the annealed
  contrast decays like `3^{-κ j}`, and the annealed blocks converge at the
  same rate, in the Loewner order and with the explicit factor `6`, to a
  deterministic symmetric positive definite limit block.
  The Schur coefficients of the limit satisfy `s̄_* = s̄ > 0` and `k̄ = −k̄ᵗ`.
* **`HCPoly.uniform_homogenization`** (Theorem C) — quantitative
  homogenization under uniform ellipticity: for laws whose fields are
  `(λ, Λ)`-elliptic almost surely, a homogenization scale `X ≥ 1` with the
  tail `P[X ≥ C (2+Λ/λ)^C t] ≤ exp(−t^d)`, above which the Dirichlet
  estimate, the correctors, the Liouville classification, the large-scale
  energy estimate and the first-order approximation of Theorem D hold, with
  dimensional constants.
* **`HCPoly.polynomial_homogenization`** (Theorem D) — homogenization with a
  random source scale: a homogenized matrix, a polynomially bounded length,
  a random homogenization radius `X` with the two-part tail
  `exp(-c t^{d-2γ}) + Ψ(c_src t)^{-1}`, and one full-probability,
  translation-invariant event on which the Dirichlet estimate in the
  negative Sobolev norms, the corrector equation and the algebraic corrector
  estimate, the first-order Liouville classification, the large-scale energy
  estimate and the large-scale first-order approximation all hold for a
  single slope-linear, stationary corrector family.
* **`HCPoly.quenched_convergence`** — the quenched all-child estimate behind
  Theorem D: a random scale with the optimal tail above which the realized
  coarse-grained blocks of every standard cell converge to the annealed
  limit block with an algebraic rate.

## Scope and faithfulness

Every theorem is rendered at the generality at which the paper proves it,
with the following conventions, which are stated in the docstrings of the
theorems themselves and inventoried in
[`CORRESPONDENCE.md`](CORRESPONDENCE.md):

- **Coefficient class.**  The coefficient space consists of the measurable
  fields, modulo almost-everywhere equality, that are locally uniformly
  elliptic: on every bounded set one pair of ellipticity constants serves
  almost every value of the field there.  The constants belong to the field
  and enter no estimate.  This is the class over which the paper states
  Theorem A.  For Theorems B, C and D the paper's qualitative class (local
  integrability of `s`, `s⁻¹` and `kᵗ s⁻¹ k`) is wider, and the containment
  of the formalized class in it is proved.
- **Dirichlet domains in Theorem D.**  The Dirichlet estimate is stated on
  the adapted cells of the homogenized matrix (translates of the image of a
  triadic cube under `s̄^{1/2}`), normalized between two concentric adapted
  ellipsoids, rather than on arbitrary bounded Lipschitz domains; and for
  supplied weak solutions rather than with existence and uniqueness.  The
  endpoint constant depends on the domain through the radii of two balls
  trapping the normalized domain.
- **Theorem C.**  Theorem C is the instance of Theorem D at exponent zero
  with a vanishing source scale and the reference block built from
  `(λ, Λ)`.  Its Dirichlet clause is therefore Theorem D's homogeneous
  negative-Sobolev estimate on adapted cells; the paper's `L²` estimate with
  a forcing term (`e.uniform.dirichlet`) is deduced from it in the paper by
  a further duality argument that is not formalized, and the tolerance `δ`
  of that estimate is accordingly absent.
- **Random radius and homogenized matrix.**  The random radius satisfies
  `X ≥ 1`; the paper's statement `X ≥ max{1, S}` is not exported.  The
  homogenized matrix of Theorem D is produced existentially and is not
  identified, in the exported statement, with the limit block of Theorem B.
- **Norms.**  Norms and energies are valued in `ℝ≥0∞`; fluxes are written
  for the skew-centered field.
- **Citations.**  Docstrings cite the paper by its own LaTeX labels.  A few of
  them cite lemmas of the companion paper HC (*Renormalization Group and
  Elliptic Homogenization in High Contrast*) by that paper's labels instead:
  `a.CFS`, `e.grok`, `e.Euc.by.tilt`, `e.tilt.by.Euc`, `e.self.dual`,
  `l.bfE.bounds`, `l.weaknorms.moreproto` and `e.euclidean.contrast.bridge`.

## Verified against a Mathlib-only statement

The development is large — about 406k lines in this repository, on top of
the 600k+-line `CoarseGraining` library it imports.  So that the central
claims can be checked without trusting either development, the main
theorems are restated using **only Mathlib** — no project definitions from
either library — in `HCPolyAudit/*/Challenge.lean`; each challenge rebuilds the
coefficient space, its local σ-fields, the coarse-graining block formalism,
the annealed blocks and the analytic carriers from Mathlib primitives and
contains one intentional statement-level `sorry`, which the corresponding
`Solution.lean` fills from the library, checked by
[`leanprover/comparator`](https://github.com/leanprover/comparator)
(see [`HCPolyAudit/README.md`](HCPolyAudit/README.md)).

| Pair | Theorem | Checked statement |
| --- | --- | --- |
| `HCPolyAudit/PolynomialEntry/` | A | `HCPoly.StatementAudit.PolynomialEntry.polynomial_entry` |
| `HCPolyAudit/AlgebraicConvergence/` | B | `HCPoly.StatementAudit.AlgebraicConvergence.algebraic_convergence` |
| `HCPolyAudit/UniformHomogenization/` | C | `HCPoly.StatementAudit.UniformHomogenization.uniform_homogenization` |
| `HCPolyAudit/PolynomialHomogenization/` | D | `HCPoly.StatementAudit.PolynomialHomogenization.polynomial_homogenization` |

## Building

The project uses [`elan`](https://github.com/leanprover/elan) and Lake; the
toolchain is pinned in [`lean-toolchain`](lean-toolchain).

```bash
# from the repository root
lake exe cache get   # prebuilt mathlib oleans (avoids a multi-hour mathlib build)
lake build           # compile the CoarseGraining dependency and the project
```

`lake exe cache get` requires the committed
[`lake-manifest.json`](lake-manifest.json), which pins the exact dependency
revisions.  The `CoarseGraining` dependency is built from source on the first
build; the project itself is about 1,956 modules.

To use the library, `import HCPoly` pulls in the whole development; the
main results are in `import HCPoly.MainResults`.

## Repository layout

```
HCPoly/
  MainResults.lean    the headline theorems, stated in full
  Setup/              the coefficient space, local σ-fields, block algebra,
                      the coarse response and the annealed contrast, geometry
  Geometry/           adapted grids, Whitney partitions, reference radii
  Analytic/           the analytic carriers behind Theorem D: normalized
                      norms, weighted Sobolev classes, weak solutions
  Annealed/           a law satisfying every standing assumption
  Frozen/             the statement surface Theorems B, C and D are proved
                      from, and the bridge from Theorem A's printed form
  Entry/              the polynomial-entry route to Theorem A
    Statements/       Theorem A and the thirteen propositions of Sections 2–5
                      it is assembled from, one theorem each
    CG/               three further propositions of the route, stated in the
                      CoarseGraining library's own vocabulary (`CG/Anchors/`)
    Setup/            the route's own vocabulary: standing assumptions, the
                      coarse response, the geometry update
    Source/           the random source scale, its Whitney decomposition and
                      its moments
    Geometry/         the route's grids, adapted cells and Whitney partitions
    Analysis/         Schatten norms and the matrix analysis of the route
    Annealed/         the annealed blocks, drifts and locality of the route
    Multiscale/       the renormalization scheme of Sections 2–5
  Provider/           the proofs of Theorems B, C and D, organized by the
                      paper's sections
  Meta/               AxiomsAudit.lean
HCPoly.lean           the root module (imports the whole library)
HCPolyAudit/          Mathlib-only comparator challenges and solutions
```

## How this was built

The Lean code in this repository was written by AI agents under the close
supervision of the authors.  Claude Fable 5.1 orchestrated the campaign —
planning, statement design, dispatch and review — and the agents that wrote
the proofs, ran the audits and did the rewriting were mostly Claude Opus 5
and GPT-5.6 Sol (at low reasoning effort); the upgrade to Lean v4.33.0, the
port of the polynomial-entry development to it and the merge of that
development into this library were carried out by DeepSeek V4.1 Flash workers
with Claude Sonnet 5 on the escalations.  The models, tooling, cost, and
review status are disclosed in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by

- **Scott Armstrong** — CNRS and Laboratoire Jacques-Louis Lions, Sorbonne
  Université; Courant Institute of Mathematical Sciences, New York University
- **Tuomo Kuusi** — Department of Mathematics and Statistics, University of
  Helsinki
- **Amélie Loher** — All Souls College, University of Oxford

If you use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong and Tuomo Kuusi were supported by the European Research Council
(ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828.

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).
