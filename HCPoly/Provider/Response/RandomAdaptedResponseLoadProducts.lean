/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseRowWeakClosure

/-!
# Calibrated response load products

These bridges expose the raw metric factor, signed load, and energy-load
bounds in the exact forms consumed by the weak-profile closure.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02

open scoped Matrix MatrixOrder

noncomputable section

/-- A calibrated primal quadratic form bounds its diagonal weak load. -/
theorem diagonal_weak_load_minus_le
    {d : ℕ} {F : BlockMat d} {Ehat : FullBlockMat d}
    (hFsym : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    (hEhat : toFullBlockMat F = Ehat) (p r : Vec d) {theta : ℝ}
    (hquad : Sum.elim (-p) r ⬝ᵥ Ehat *ᵥ Sum.elim (-p) r ≤
      4 * Real.sqrt theta) :
    diagonalWeakLoadMinus F p r ≤ 2 * Real.sqrt (Real.sqrt theta) := by
  have hsq : diagonalWeakLoadMinus F p r ^ 2 ≤ 4 * Real.sqrt theta := by
    rw [sq_diagonalWeakLoadMinus hFsym hFpd,
      blockVecDot_blockMatVecMul_eq_dotProduct, hEhat,
      to_full_block_vec_pair_row_weak]
    exact hquad
  have hroot := le_sqrt_of_sq_le (diagonalWeakLoadMinus_nonneg F p r) hsq
  calc
    diagonalWeakLoadMinus F p r ≤ Real.sqrt (4 * Real.sqrt theta) := hroot
    _ = 2 * Real.sqrt (Real.sqrt theta) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by norm_num)]

/-- A calibrated adjoint quadratic form bounds its independent diagonal weak
load. -/
theorem diagonal_weak_load_plus_le
    {d : ℕ} {F : BlockMat d} {Ehat : FullBlockMat d}
    (hFsym : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    (hEhat : toFullBlockMat F = Ehat) (p r : Vec d) {theta : ℝ}
    (hquad : Sum.elim p r ⬝ᵥ Ehat *ᵥ Sum.elim p r ≤
      4 * Real.sqrt theta) :
    diagonalWeakLoadPlus F p r ≤ 2 * Real.sqrt (Real.sqrt theta) := by
  have hsq : diagonalWeakLoadPlus F p r ^ 2 ≤ 4 * Real.sqrt theta := by
    rw [sq_diagonalWeakLoadPlus hFsym hFpd,
      blockVecDot_blockMatVecMul_eq_dotProduct, hEhat,
      to_full_block_vec_pair_row_weak]
    exact hquad
  have hroot := le_sqrt_of_sq_le (diagonalWeakLoadPlus_nonneg F p r) hsq
  calc
    diagonalWeakLoadPlus F p r ≤ Real.sqrt (4 * Real.sqrt theta) := hroot
    _ = 2 * Real.sqrt (Real.sqrt theta) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by norm_num)]

/-- A unit load pairing and the calibrated load square bound control the
profile energy load. -/
theorem profile_energy_load_le_sqrt_five
    {d : ℕ} {L theta : ℝ} {p r : Vec d}
    (htheta : 1 ≤ theta) (hpair : vecDot p r = 1)
    (hLsq : L ^ 2 ≤ 4 * Real.sqrt theta) :
    profileEnergyLoad L p r ≤
      Real.sqrt 5 * Real.sqrt (Real.sqrt theta) := by
  apply lambda_le (profileEnergyLoad_nonneg L p r) htheta
  · rw [sq_profileEnergyLoad, hpair, abs_one]
  · exact hLsq

end

end Homogenization.HighContrast.Response
