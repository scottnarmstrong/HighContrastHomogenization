/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Annealed.Integrability

/-!
# Positivity of the annealed block under the coarse ellipticity assumption

The annealed block at a centered cube is the expectation of a family of positive
definite coarse responses, and is therefore itself positive definite: the
well-formedness that `e.Theta.m` presupposes for `Θ_m`.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The positivity of the annealed block** under `e.coarse.ellipticity`:
the annealed block at every scale is the honest expectation of a positive
definite family, and is itself positive definite. -/
theorem blockPosDef_annealedBlock_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d m)) :=
  blockPosDef_annealedBlock_centeredCube m
    (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag m)

end

end HighContrast
end Homogenization
