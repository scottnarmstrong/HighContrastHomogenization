/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.MainResults

/-!
# Axiom dependencies of the main results

Building this module prints the axiom dependencies of the theorems of
`HCPoly.MainResults`.  Each must report exactly the three standard foundational
axioms of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

This file is intentionally not imported by the library root, so the report runs
only when it is built explicitly, with `lake build HCPoly.Meta.AxiomsAudit`.
-/

#print axioms HCPoly.polynomial_entry
#print axioms HCPoly.algebraic_convergence
#print axioms HCPoly.uniform_homogenization
#print axioms HCPoly.polynomial_homogenization
#print axioms HCPoly.quenched_convergence
