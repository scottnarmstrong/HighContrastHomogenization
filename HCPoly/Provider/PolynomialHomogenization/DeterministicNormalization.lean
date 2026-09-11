/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.DirichletDomain
import Homogenization.Book.Ch03.Definitions

/-!
# Deterministic identity normalization

The inverse square root of a positive definite symmetric part normalizes that
matrix to the positive scalar identity required by the deterministic
coarse-graining comparison.
-/

namespace Homogenization
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The identity comparison coefficient in the Chapter 3 carrier. -/
def identityConstantCoeffMatrix (d : ℕ) : Book.Ch03.ConstantCoeffMatrix d where
  matrix := 1
  isSymm := Matrix.isSymm_one
  lam := 1
  Lam := 1
  lam_pos := by norm_num
  lam_le_Lam := le_rfl
  elliptic := by
    simpa only [one_smul] using
      (isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) (by norm_num))

/-- The matrix carried by the identity comparison coefficient is the identity. -/
@[simp] theorem identityConstantCoeffMatrix_matrix (d : ℕ) :
    (identityConstantCoeffMatrix d).matrix = (1 : Mat d) :=
  rfl

/-- The identity comparison coefficient satisfies the upstream positivity
contract. -/
theorem identityConstantCoeffMatrix_isPositiveScalarMatrix (d : ℕ) :
    IsPositiveScalarMatrix (identityConstantCoeffMatrix d).matrix := by
  refine ⟨1, by norm_num, ?_⟩
  simp only [identityConstantCoeffMatrix_matrix, one_smul]

end

end HighContrast
end Homogenization
