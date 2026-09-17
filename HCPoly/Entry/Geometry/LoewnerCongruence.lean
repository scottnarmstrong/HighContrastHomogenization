import HCPoly.Entry.Geometry.PositiveSqrt
import HCPoly.Entry.Geometry.SpectralExtrema
import HCPoly.Entry.Setup.SpectralBound

/-!
# Congruence for the Loewner order

This file proves the quadratic-form congruence layer needed to compare the
relative matrix `m₀^{-1/2} m₁ m₀^{-1/2}` with the `MatLoewnerLE`
thresholds.  The congruence is purely by substitution in the quadratic form;
no commutativity between the two endpoint matrices is used.
-/

open Homogenization.HighContrast (matSqrt matSqrt_spec)
namespace Homogenization.HighContrast.Geometry

open Matrix
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem quadForm_congr (A P : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose P * A * P) x) =
      vecDot (matVecMul P x) (matVecMul A (matVecMul P x)) := by
  rw [← matVecMul_mul (matTranspose P * A) P x]
  rw [← matVecMul_mul (matTranspose P) A (matVecMul P x)]
  rw [vecDot_matVecMul_transpose]

/-- Congruence preserves the Loewner order. -/
theorem matLoewnerLE_congr {A B P : Mat d} (h : MatLoewnerLE A B) :
    MatLoewnerLE (matTranspose P * A * P) (matTranspose P * B * P) := by
  intro x
  simpa [quadForm_congr] using h (matVecMul P x)

/-- Invertible congruence reflects and preserves the Loewner order. -/
theorem matLoewnerLE_congr_iff_of_isUnit_det {A B P : Mat d} (hP : IsUnit P.det) :
    MatLoewnerLE A B ↔
      MatLoewnerLE (matTranspose P * A * P) (matTranspose P * B * P) := by
  constructor
  · exact matLoewnerLE_congr
  · intro h y
    have hsurj : Function.Surjective (matVecMul P) := by
      simpa [matVecMul] using!
        (Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det P).mpr hP))
    obtain ⟨x, rfl⟩ := hsurj y
    simpa [quadForm_congr] using h x

/-- The square root of the inverse of a positive matrix is positive definite. -/
theorem matSqrt_inv_posDef {m : Mat d} (hm : m.PosDef) : (matSqrt m⁻¹).PosDef := by
  rw [matSqrt_eq_cfc_sqrt hm.inv.posSemidef]
  exact posDef_sqrt hm.inv

/-- The inverse square-root congruence sends a positive matrix to the identity. -/
theorem matSqrt_inv_mul_self_mul_matSqrt_inv {m : Mat d} (hm : m.PosDef) :
    matSqrt m⁻¹ * m * matSqrt m⁻¹ = 1 := by
  let S : Mat d := matSqrt m⁻¹
  have hSS : S * S = m⁻¹ := (matSqrt_spec hm.inv.posSemidef).2
  have hmDet : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp hm.isUnit
  have hright : S * (S * m) = 1 := by
    rw [← mul_assoc, hSS, Matrix.nonsing_inv_mul m hmDet]
  have hSinv : S⁻¹ = S * m := Matrix.inv_eq_right_inv hright
  have hSDet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp (matSqrt_inv_posDef hm).isUnit
  calc
    S * m * S = S⁻¹ * S := by rw [hSinv]
    _ = 1 := Matrix.nonsing_inv_mul S hSDet

end

end Homogenization.HighContrast.Geometry
