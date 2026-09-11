/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.IdentityGrid
import HCPoly.Provider.Initialization.Boundary

/-!
# The Euclidean grid as a rounded adapted grid

The bootstrap of the small-contrast window compares the adapted mean on the
selection grid with the annealed block on a centered cube.  The comparison is
read through the tilt scalarization, whose reference argument is an adapted
mean on a *rounded* grid; so the Euclidean cube must itself be presented as an
adapted cell of a rounded grid.

Rounding fixes the identity witness at every nonnegative alignment: each
diagonal entry rounds the integer `3^j` and each off-diagonal entry is zero.
The identity-grid file records this under a coupled window; the
bootstrap has no window, and the statement needs none — nonnegativity of the
alignment is the whole hypothesis.
-/

namespace Homogenization.HighContrast.Quenched

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **Rounding fixes the identity witness** at every nonnegative alignment.
This is the window-free form of the `Initialization.roundedGrid_one`. -/
theorem roundedGrid_one_of_nonneg [Nonempty (Fin d)] {j : ℤ} (hj : 0 ≤ j) :
    roundedGrid j (1 : Mat d) = (1 : Mat d) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have hspec : specBound ((1 : Mat d)⁻¹) = 1 := by
    rw [inv_one, specBound_eq_norm Matrix.PosSemidef.one, norm_one]
  ext i k
  rw [Recurrence.roundedGrid_apply, hspec, Real.sqrt_one, Recurrence.matSqrt_one]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply_eq, mul_one, zpow_natCast]
    have hceil : ⌈(3 : ℝ) ^ n⌉ = (((3 ^ n : ℕ) : ℤ)) := by
      simpa only [Nat.cast_ofNat, Nat.cast_pow] using
        (Int.ceil_natCast (R := ℝ) (3 ^ n))
    rw [hceil, Int.cast_natCast, zpow_neg, zpow_natCast, Nat.cast_pow]
    exact inv_mul_cancel₀ (by positivity)
  · simp [hik, zpow_natCast]

/-- The Euclidean grid is a rounded adapted grid at every admissible
alignment. -/
theorem isRoundedGrid_one [Nonempty (Fin d)] {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) : IsRoundedGrid l (1 : Mat d) :=
  ⟨hl, 1, Matrix.PosDef.one,
    (roundedGrid_one_of_nonneg ((Int.natCast_nonneg _).trans hl)).symm⟩

/-- The adapted mean of the Euclidean grid is the annealed block of the
centered cube. -/
theorem adaptedMean_one (P : Measure (CoeffSpace d)) (m : ℤ) :
    adaptedMean P (1 : Mat d) m = annealedBlock P (centeredCube d m) := by
  rw [adaptedMean, Initialization.adaptedCell_one]

end

end Homogenization.HighContrast.Quenched
