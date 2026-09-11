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
paper's Sections 2–5 — scale selection, contraction on one adapted grid,
change of geometry, initialization, global selection, and response and
Euclidean transfer — is formalized in full, and so are the deductions of
Section 6 that the theorems below state.

All four theorems of the paper's introduction — Theorems A, B, C and D — are
formalized and proved, each exported in the paper's own form in
`HCPoly/MainResults.lean` and each checked against a Mathlib-only
restatement by the Lean comparator.  Theorem C is obtained as the instance
of Theorem D for uniformly elliptic laws; its Dirichlet clause is exported
in the negative-Sobolev form of Theorem D rather than the paper's `L²`
form with a forcing term, as explained below.

- **1,656 Lean source files, 332,381 lines** (including the comparator
  audit surface; the library itself is 1,640 files and 325,097 lines).
- **No `sorry`** anywhere in the library.  (Each Mathlib-only comparator
  challenge in `Audit/` contains its single intentional statement-level
  `sorry`, filled by the corresponding solution file.)
- **No custom `axiom`.**  The main theorems reduce to `mathlib`'s three
  standard foundational axioms — `propext`, `Classical.choice`, `Quot.sound` —
  verified by
  [`HCPoly/Meta/AxiomsAudit.lean`](HCPoly/Meta/AxiomsAudit.lean).
- Pinned to Lean `v4.26.0`, `mathlib` `v4.26.0`, and `CoarseGraining` at a
  fixed revision.

## Main results

The headline theorems are stated in full in
[`HCPoly/MainResults.lean`](HCPoly/MainResults.lean), each proved by direct
application to its certified counterpart, so the statements displayed there
are faithful to the verified ones.

* **`HCPoly.polynomial_entry`** (Theorem A of the paper) — polynomial entry
  into small contrast: for every tolerance `σ ∈ (0,1]` there is a constant
  `C(σ, d, γ)` such that, for every law satisfying the standing assumptions,
  the annealed contrast `Θ_m` is at most `1 + σ` at a deterministic
  generation `m_ent ≤ ⌈C log₃(2 + Π K)⌉`; equivalently, the corresponding
  length `3^{m_ent}` is at most `3 (2 + Π K)^C`.
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
  and enter no estimate; the paper's qualitative class (local integrability
  of `s`, `s⁻¹` and `kᵗ s⁻¹ k`) is wider, and the containment of the
  formalized class in it is proved.
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

## Verified against a Mathlib-only statement

The development is large — about 325k lines in this repository, on top of
the 600k+-line `CoarseGraining` library it imports.  So that the central
claims can be checked without trusting either development, the main
theorems are restated using **only Mathlib** — no project definitions from
either library — in `Audit/*/Challenge.lean`; each challenge rebuilds the
coefficient space, its local σ-fields, the coarse-graining block formalism,
the annealed blocks and the analytic carriers from Mathlib primitives and
contains one intentional statement-level `sorry`, which the corresponding
`Solution.lean` fills from the library, checked by
[`leanprover/comparator`](https://github.com/leanprover/comparator)
(see [`Audit/README.md`](Audit/README.md)).

| Pair | Theorem | Checked statement |
| --- | --- | --- |
| `Audit/PolynomialEntry/` | A | `HCPoly.StatementAudit.PolynomialEntry.polynomial_entry` |
| `Audit/AlgebraicConvergence/` | B | `HCPoly.StatementAudit.AlgebraicConvergence.algebraic_convergence` |
| `Audit/UniformHomogenization/` | C | `HCPoly.StatementAudit.UniformHomogenization.uniform_homogenization` |
| `Audit/PolynomialHomogenization/` | D | `HCPoly.StatementAudit.PolynomialHomogenization.polynomial_homogenization` |

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
build; the project itself is about 1,640 modules.

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
  Frozen/             the certified statement surface: the four main
                      theorems' sources and the propositions feeding them
  Provider/           the proofs, organized by the paper's sections
  Meta/               AxiomsAudit.lean
HCPoly.lean           the root module (imports the whole library)
Audit/                Mathlib-only comparator challenges and solutions
```

## How this was built

The Lean code in this repository was written by AI agents under the close
supervision of the authors.  Claude Fable 5.1 orchestrated the campaign —
planning, statement design, dispatch and review — and the agents that wrote
the proofs, ran the audits and did the rewriting were mostly Claude Opus 5
and GPT-5.6 Sol (at low reasoning effort).  The models, tooling, cost, and
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
