# HighContrastHomogenization

A machine-checked **Lean 4** formalization of the manuscript
*Homogenization at a polynomial scale in high contrast*
(Scott Armstrong, Tuomo Kuusi, and Amélie Loher). It is built on
[`mathlib`](https://github.com/leanprover-community/mathlib4) and the public
[`CoarseGraining`](https://github.com/scottnarmstrong/CoarseGraining)
homogenization library.

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
high-contrast homogenization theory of Armstrong and Kuusi [AK25]
([*Renormalization group and elliptic homogenization in high contrast*](https://doi.org/10.1007/s00222-025-01370-9),
Invent. Math. 2025)
gives algebraic convergence of the annealed coarse-grained matrices,
quantitative Dirichlet homogenization, corrector estimates, a first-order
Liouville theorem, and large-scale regularity above a single random radius
whose tail has a stretched-exponential term and a rescaled copy of the
source-tail bound.

This repository proves the paper's renormalization results from Sections 2–5,
including scale selection, matrix averaging, propagation across adapted grids,
and the polynomial entry theorem. It also formalizes the convergence and
homogenization deductions of Section 6. The four introductory results,
Theorems A–D, are available in [`HCPoly/MainResults.lean`](HCPoly/MainResults.lean).
Each has a Mathlib-only restatement checked with
[`leanprover/comparator`](https://github.com/leanprover/comparator). The
differences between the formal statements and the printed results are described
under [Scope and faithfulness](#scope-and-faithfulness).

- **About 380,000 lines of Lean** across the library and its comparator checks.
- **No `sorry`** anywhere in the library.  (Each Mathlib-only comparator
  challenge in `HCPolyAudit/` contains its single intentional statement-level
  `sorry`, filled by the corresponding solution file.)
- **No custom `axiom`.**  The main theorems reduce to `mathlib`'s three
  standard foundational axioms — `propext`, `Classical.choice`, `Quot.sound` —
  verified by
  [`HCPoly/Meta/AxiomsAudit.lean`](HCPoly/Meta/AxiomsAudit.lean).
- Pinned to Lean `v4.33.0`, `mathlib` `v4.33.0`, and `CoarseGraining` at a
  fixed revision.

## Main results

The headline theorems are stated in full in
[`HCPoly/MainResults.lean`](HCPoly/MainResults.lean). Their statements and proofs
can be read alongside the paper-to-Lean map in
[`CORRESPONDENCE.md`](CORRESPONDENCE.md).

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

The formal statements have the following scope and rendering conventions.
These differences from the printed statements are also recorded in the
theorem docstrings and inventoried in
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
- **Citations.**  Docstrings cite the paper by its own LaTeX labels. A few
  cite lemmas from [AK25] by that paper's labels instead:
  `a.CFS`, `e.grok`, `e.Euc.by.tilt`, `e.tilt.by.Euc`, `e.self.dual`,
  `l.bfE.bounds`, `l.weaknorms.moreproto` and `e.euclidean.contrast.bridge`.

## Consistency checks of the definitions

Formal definitions need checks beyond their theorem proofs. For example, the
families used to define the dual norms must contain tests, the coefficient
class must contain fields satisfying the assumptions, and the formal contrast
must equal the spectral minimum appearing in the paper. The modules under
`HCPoly/Consistency/` establish these properties one definition at a time.
They are checks on the interpretation of the statements, not results claimed
by the paper.

| file | definition checked |
| --- | --- |
| [`AdmissibleTests.lean`](HCPoly/Consistency/AdmissibleTests.lean) | the admissible-test families of the two normalized dual norms are not empty |
| [`AspectRatioSharpness.lean`](HCPoly/Consistency/AspectRatioSharpness.lean) | the lower bound `1 ≤ Π` on the reference aspect ratio needs the Schur ordering |
| [`ClosureH1aNecessity.lean`](HCPoly/Consistency/ClosureH1aNecessity.lean) | boundedness of the domain cannot be dropped from the `H¹_a(V)` closure family |
| [`ClosureH1aPairing.lean`](HCPoly/Consistency/ClosureH1aPairing.lean) | the weak-gradient relation on the `H¹_a` classes is an identity between convergent integrals |
| [`ConvexDilation.lean`](HCPoly/Consistency/ConvexDilation.lean) | the membership classes are reached from smoothness on the domain by dilation |
| [`Dissolution.lean`](HCPoly/Consistency/Dissolution.lean) | the fallback value in the coarse block response is never attained |
| [`DomainCompleteness.lean`](HCPoly/Consistency/DomainCompleteness.lean) | the domains of the Dirichlet estimate are exactly the nonempty bounded open convex ones |
| [`Necessity.lean`](HCPoly/Consistency/Necessity.lean) | what the measurability conjunct of the local Sobolev class excludes |
| [`PrintedForm.lean`](HCPoly/Consistency/PrintedForm.lean) | the intrinsic contrast and `Λ_0` are the printed minima over skew matrices |
| [`QualitativeClass.lean`](HCPoly/Consistency/QualitativeClass.lean) | the coefficient class used here lies inside the paper's qualitative class |
| [`WitnessField.lean`](HCPoly/Consistency/WitnessField.lean) | the coefficient space has its reference point, fixed by every integer translation |
| [`WitnessSigmaField.lean`](HCPoly/Consistency/WitnessSigmaField.lean) | the local σ-fields of the coefficient space separate points |

## Verified against a Mathlib-only statement

To make the central claims independently inspectable, the main theorems are
restated using **only Mathlib** — no project definitions from
either library — in `HCPolyAudit/*/Challenge.lean`; each challenge rebuilds the
coefficient space, its local σ-fields, the coarse-graining block formalism,
the annealed blocks and the analytic carriers from Mathlib primitives and
contains one intentional statement-level `sorry`, which the corresponding
`Solution.lean` fills from the library, checked by
[`leanprover/comparator`](https://github.com/leanprover/comparator)
(see [`HCPolyAudit/README.md`](HCPolyAudit/README.md)).

| Comparator configuration | Theorem | Checked statement |
| --- | --- | --- |
| [`HCPolyAudit/PolynomialEntry/comparator.json`](HCPolyAudit/PolynomialEntry/comparator.json) | A | `HCPoly.StatementAudit.PolynomialEntry.polynomial_entry` |
| [`HCPolyAudit/AlgebraicConvergence/comparator.json`](HCPolyAudit/AlgebraicConvergence/comparator.json) | B | `HCPoly.StatementAudit.AlgebraicConvergence.algebraic_convergence` |
| [`HCPolyAudit/UniformHomogenization/comparator.json`](HCPolyAudit/UniformHomogenization/comparator.json) | C | `HCPoly.StatementAudit.UniformHomogenization.uniform_homogenization` |
| [`HCPolyAudit/PolynomialHomogenization/comparator.json`](HCPolyAudit/PolynomialHomogenization/comparator.json) | D | `HCPoly.StatementAudit.PolynomialHomogenization.polynomial_homogenization` |

For [Palomar](https://palomar-registry.org/how-to-submit), each configuration
is a separate result submission at the same public commit.

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
build; the project itself is about 1,561 modules.

To use the library, `import HCPoly` pulls in the whole development; the
main results are in `import HCPoly.MainResults`.

## Repository layout

| Location | Where to start |
| --- | --- |
| [`HCPoly/MainResults.lean`](HCPoly/MainResults.lean) | Full statements of Theorems A–D and the quenched convergence result |
| [`HCPoly/Entry/Statements/`](HCPoly/Entry/Statements/) | The polynomial entry theorem and the propositions of Sections 2–5 used to prove it |
| [`HCPoly/Provider/`](HCPoly/Provider/) | Proofs of the convergence and homogenization results |
| [`HCPoly/Setup/`](HCPoly/Setup/) and [`HCPoly/Analytic/`](HCPoly/Analytic/) | Coefficient fields, block quantities, Sobolev spaces and weak solutions |
| [`HCPoly/Consistency/`](HCPoly/Consistency/) | Checks that the formal definitions have the intended mathematical meaning |
| [`HCPolyAudit/`](HCPolyAudit/) | Mathlib-only comparator challenges and their solutions |
| [`CORRESPONDENCE.md`](CORRESPONDENCE.md) | The paper-to-Lean map, including the precise scope differences |

[`HCPoly.lean`](HCPoly.lean) imports the whole library. The detailed
organization of each proof can be followed from the theorem links in
`CORRESPONDENCE.md`.

## How this was built

The Lean code was written with AI coding agents under the authors' supervision.
The authors reviewed the mathematical statements, and Lean checks the proofs
against those statements. The models, tools, cost information, and review
status are recorded in
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
Amélie Loher acknowledges support from the Fondation Sciences Mathématiques de Paris.

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).
