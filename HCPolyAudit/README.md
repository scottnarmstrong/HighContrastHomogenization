# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the main
theorems of the formalization of *Homogenization at a polynomial scale in
high contrast* (Armstrong–Kuusi–Loher).  Each comparator lives in its own
subdirectory:

| Directory | Checked theorem | Paper |
| --- | --- | --- |
| `PolynomialEntry/` | `HCPoly.StatementAudit.PolynomialEntry.polynomial_entry` | Theorem A, `t.polynomial.entry` |
| `AlgebraicConvergence/` | `HCPoly.StatementAudit.AlgebraicConvergence.algebraic_convergence` | Theorem B, `t.algebraic.convergence` |
| `UniformHomogenization/` | `HCPoly.StatementAudit.UniformHomogenization.uniform_homogenization` | Theorem C, `t.uniform.homogenization` |
| `PolynomialHomogenization/` | `HCPoly.StatementAudit.PolynomialHomogenization.polynomial_homogenization` | Theorem D, `t.random.homogenization` |

Each directory also carries a `DESIGN.md` recording the provenance of every
rebuilt declaration, the bridge inventory, and the presentation deltas in full;
the module docstring of each `Challenge.lean` carries the statement in words,
the standing assumptions, and the differences a reader needs to compare the
Lean statement with the printed theorem.

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem — the coefficient space of locally
uniformly elliptic fields modulo almost-everywhere equality and its local
σ-fields, the integer translations, the triadic and adapted geometry, the
coarse-graining block formalism and the annealed blocks, the reference
aspect ratio and the annealed contrast, the source gauge conditions, and
(for Theorems C and D) the normalized fractional and negative Sobolev norms, the
weighted solution classes, weak solutions, ellipsoids and the Liouville
class — states the theorem, and ends with one `sorry`, the proof being
checked.  Each `SolutionBasic.lean` is a verbatim copy of the challenge's
vocabulary, again Mathlib-only; each `Solution.lean` imports the repository
and proves the byte-identical statement through the bridges in `Support/`.

## Reproducing the checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone
against this repository's Mathlib toolchain:

```bash
bash HCPolyAudit/check_standalone.sh HCPolyAudit/PolynomialEntry/Challenge.lean
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per file.  The comparator itself runs as

```bash
lake build HCPolyAudit
lake env comparator HCPolyAudit/PolynomialEntry/comparator.json
```

with `leanprover/comparator` (commit `32bd61d`), `lean4export` at the
project's toolchain tag `v4.35.0-rc2` (commit `6cea977`) and `landrun`
(`v0.1.18`) on the path, the same pins the continuous-integration workflow
builds (see the comparator's README for the sandboxed `systemd-run` form);
the acceptance line is `Your solution is okay!`.

**Status.**  All four comparators are checked and passing.  Each
`HCPolyAudit/*/Solution.lean` imports the repository and proves the byte-identical
challenge statement through the bridges in `HCPolyAudit/Support/`;
`leanprover/comparator` confirms identical elaborated statements, walks the
full dependency closure of each challenge theorem constant by constant,
replays the solution through the Lean kernel, and prints its acceptance
line — `Your solution is okay!` — for all four pairs, with the permitted
axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
