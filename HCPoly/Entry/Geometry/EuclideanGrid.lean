import HCPoly.Entry.Geometry.RoundedGrid
import HCPoly.Entry.Geometry.AdaptedCellTransport

/-!
# The Euclidean grid

The initialization uses the literal
Euclidean grid `(1 : Mat d)`, while the rounded-grid infrastructure is stated
for `Geometry.explicitRoundedGrid jStar m`.  This file records the exact identity-grid
bridges used to move between those surfaces.
-/

open Homogenization.HighContrast (adaptedCell adaptedCellTranslate centeredCube standardCell)
namespace Homogenization.HighContrast.Geometry

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

noncomputable section

/-- The unrounded grid of the Euclidean metric is the identity. -/
theorem unroundedGrid_one [NeZero d] : unroundedGrid (1 : Mat d) = 1 := by
  unfold unroundedGrid
  rw [inv_one, norm_one, Real.sqrt_one, one_smul]
  exact CFC.sqrt_one

/-- The rounded grid of the Euclidean metric is the identity. -/
theorem explicitRoundedGrid_one [NeZero d] (jStar : ℕ) :
    explicitRoundedGrid jStar (1 : Mat d) = 1 := by
  ext a b
  rw [explicitRoundedGrid_apply, unroundedGrid_one]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.one_apply_eq]
    rw [mul_one]
    have hceil : ⌈(3 : ℝ) ^ jStar⌉ = ((3 : ℕ) ^ jStar : ℤ) := by
      rw [show (3 : ℝ) ^ jStar = (((3 : ℕ) ^ jStar : ℕ) : ℝ) by norm_num]
      exact Int.ceil_natCast ((3 : ℕ) ^ jStar)
    rw [hceil]
    have hcast : (((3 : ℕ) ^ jStar : ℤ) : ℝ) = (3 : ℝ) ^ jStar := by norm_num
    rw [hcast]
    have hpow : (0 : ℝ) < (3 : ℝ) ^ jStar := by positivity
    field_simp [hpow.ne']
  · simp only [Matrix.one_apply_ne hab, mul_zero, Int.ceil_zero, Int.cast_zero, mul_zero]

/-- The Euclidean metric is positive definite. -/
theorem one_posDef (d : ℕ) : (1 : Mat d).PosDef :=
  Matrix.PosDef.one

/-- The literal Euclidean grid is invertible. -/
theorem isUnit_one_grid (d : ℕ) : IsUnit (1 : Mat d) :=
  (one_posDef d).isUnit

/-- The adapted cell for the identity grid is the centered standard cell. -/
theorem adaptedCell_one (j : ℤ) :
    adaptedCell (1 : Mat d) j = standardCell d j 0 := by
  rw [← centeredCube_eq_standardCell (d := d) j]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [matVecMul_eq_mulVec] using hv
  · intro hx
    exact ⟨x, hx, by simp [matVecMul_eq_mulVec]⟩

/-- The translated adapted cell at the origin is the standard cell. -/
theorem adaptedCellTranslate_one_zero (j : ℤ) :
    adaptedCellTranslate (1 : Mat d) j 0 = standardCell d j 0 := by
  rw [adaptedCellTranslate, adaptedCell_one]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hx
    exact ⟨x, hx, by simp⟩

/-- Centered triadic cubes are monotone in the generation. -/
theorem centeredCube_subset_of_le {j k : ℤ} (hjk : j ≤ k) :
    centeredCube d j ⊆ centeredCube d k := by
  intro x hx
  rw [mem_centeredCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ k :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hjk
  have hpos : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hpos' : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  constructor
  · nlinarith [(hx i).1]
  · nlinarith [(hx i).2]

/-- Identity adapted cells lie in the source window whenever their generation does. -/
theorem adaptedCell_one_subset_centeredCube (j : ℤ) {jStar : ℕ}
    (hj : j ≤ 2 * (jStar : ℤ)) :
    adaptedCell (1 : Mat d) j ⊆ centeredCube d (2 * (jStar : ℤ)) := by
  rw [adaptedCell_one, ← centeredCube_eq_standardCell (d := d) j]
  exact centeredCube_subset_of_le hj

end

end Homogenization.HighContrast.Geometry
