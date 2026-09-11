/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Entry.EuclideanAdapter
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootCoefficient
import HCPoly.Provider.Regularity.RoundedAffineMap
import HCPoly.Provider.Selection.EnclosureGeometry

/-!
# Rounded outer cells inside one normalized-root parent

The aligned base-rounded cells below a fixed outer scale form finite spatial
rows.  One generation offset, controlled by the rounded intrinsic
eccentricity, encloses every cell in every row inside the same exact
normalized-root parent.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem adaptedCell_subset_adaptedCell_add_of_norm_inv_mul_le
    [NeZero d] {p q : Mat d} (hq : q.PosDef) {M : ℤ} {G : ℕ}
    (hsize : ‖q⁻¹ * p‖ * Real.sqrt d ≤ (3 : ℝ) ^ (G : ℤ)) :
    adaptedCell p M ⊆ adaptedCell q (M + (G : ℤ)) := by
  have hsmall : adaptedCell (q⁻¹ * p) M ⊆
      centeredCube d (M + (G : ℤ)) :=
    Selection.adaptedCell_subset_centeredCube_add
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) hsize
  rintro x ⟨y, hy, rfl⟩
  have hz : matVecMul (q⁻¹ * p) y ∈
      centeredCube d (M + (G : ℤ)) :=
    hsmall ⟨y, hy, rfl⟩
  refine ⟨matVecMul (q⁻¹ * p) y, hz, ?_⟩
  rw [matVecMul_mul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv q (isUnit_det_of_posDef hq), Matrix.one_mul]

end

end Transport
end HighContrast
end Homogenization
