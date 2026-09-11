/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects

/-!
# Decay sums for the two-grid bridge

This file proves the scalar geometric estimates used to compare boundary rows
with the weighted determinant drift and to sum the shifted source remainder.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

noncomputable section

/-! ## The comparison-row weight -/

/-- A convex split of an exponent is bounded by the larger endpoint. -/
theorem rpow_neg_max_le_split {rho l x : ℝ} (hrho₀ : 0 ≤ rho)
    (hrho₁ : rho ≤ 1) :
    (3 : ℝ) ^ (-max l x) ≤
      (3 : ℝ) ^ (-(1 - rho) * l) * (3 : ℝ) ^ (-rho * x) := by
  have hleft : (1 - rho) * l ≤ (1 - rho) * max l x :=
    mul_le_mul_of_nonneg_left (le_max_left l x) (sub_nonneg.mpr hrho₁)
  have hright : rho * x ≤ rho * max l x :=
    mul_le_mul_of_nonneg_left (le_max_right l x) hrho₀
  have hconvex : (1 - rho) * l + rho * x ≤ max l x := by
    calc
      (1 - rho) * l + rho * x ≤
          (1 - rho) * max l x + rho * max l x := add_le_add hleft hright
      _ = max l x := by ring
  calc
    (3 : ℝ) ^ (-max l x) ≤
        (3 : ℝ) ^ (-((1 - rho) * l + rho * x)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hconvex)
    _ = (3 : ℝ) ^ (-(1 - rho) * l) * (3 : ℝ) ^ (-rho * x) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring

/-- Faster geometric decay is bounded by the slower decay with the printed
linear prefactor. -/
theorem fast_decay_le_linear_slow_decay {a rho N : ℝ} (hN : 0 ≤ N)
    (hrho : rho ≤ a) :
    (3 : ℝ) ^ (-a * N) ≤ (1 + N) * (3 : ℝ) ^ (-rho * N) := by
  have hexp : -a * N ≤ -rho * N := by
    calc
      -a * N = -(a * N) := by ring
      _ ≤ -(rho * N) := neg_le_neg (mul_le_mul_of_nonneg_right hrho hN)
      _ = -rho * N := by ring
  have hpow : (3 : ℝ) ^ (-a * N) ≤ (3 : ℝ) ^ (-rho * N) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hslow : 0 ≤ (3 : ℝ) ^ (-rho * N) := Real.rpow_nonneg (by norm_num) _
  exact hpow.trans <| by
    calc
      (3 : ℝ) ^ (-rho * N) = 1 * (3 : ℝ) ^ (-rho * N) := by ring
      _ ≤ (1 + N) * (3 : ℝ) ^ (-rho * N) :=
        mul_le_mul_of_nonneg_right (by linarith only [hN]) hslow

/-! ## The shifted source convolution -/

private theorem source_convolution_exponent_le {rho a l N s : ℝ}
    (hrho₀ : 0 ≤ rho) (hrhoa : rho ≤ a) (hl : 1 ≤ l) (hs : 0 ≤ s) :
    -rho * (N - s - 1) + -a * s ≤ rho * l + -rho * N := by
  have hgap : (rho - a) * s ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrhoa) hs
  have hrl : rho ≤ rho * l := by
    calc
      rho = rho * 1 := by ring
      _ ≤ rho * l := mul_le_mul_of_nonneg_left hl hrho₀
  calc
    -rho * (N - s - 1) + -a * s = -rho * N + rho + (rho - a) * s := by
      ring
    _ ≤ (-rho * N + rho) + 0 := add_le_add_right hgap _
    _ = -rho * N + rho := by ring
    _ ≤ -rho * N + rho * l := by
      calc
        -rho * N + rho = rho + -rho * N := by ring
        _ ≤ rho * l + -rho * N := add_le_add_left hrl _
        _ = -rho * N + rho * l := by ring
    _ = rho * l + -rho * N := by ring

/-- Each continued source term is bounded by the shifted-remainder envelope. -/
theorem source_convolution_term_le {rho a : ℝ} {l N s : ℤ}
    (hrho₀ : 0 ≤ rho) (hrhoa : rho ≤ a) (hl : 1 ≤ l) (hls : l ≤ s) :
    (3 : ℝ) ^ (-rho * ((N : ℝ) - (s : ℝ) - 1)) *
        (3 : ℝ) ^ (-a * (s : ℝ)) ≤
      (3 : ℝ) ^ (rho * (l : ℝ)) * (3 : ℝ) ^ (-rho * (N : ℝ)) := by
  have hlreal : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hsreal : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast le_trans (by omega) hls
  calc
    (3 : ℝ) ^ (-rho * ((N : ℝ) - (s : ℝ) - 1)) *
          (3 : ℝ) ^ (-a * (s : ℝ)) =
        (3 : ℝ) ^
          (-rho * ((N : ℝ) - (s : ℝ) - 1) + -a * (s : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ ≤ (3 : ℝ) ^ (rho * (l : ℝ) + -rho * (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (source_convolution_exponent_le hrho₀ hrhoa hlreal hsreal)
    _ = (3 : ℝ) ^ (rho * (l : ℝ)) * (3 : ℝ) ^ (-rho * (N : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

end

end Bridge
end HighContrast
end Homogenization
