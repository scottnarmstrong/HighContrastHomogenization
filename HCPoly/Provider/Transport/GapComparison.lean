/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.GainConvexity
import HCPoly.Provider.Recurrence.SchattenSpectral

/-!
# The two gain functions of the transport, and the spectral size above the identity

The transport subsection carries two gain functions on blocks above the
identity: the one the fixed-grid section already uses,
`𝔥_Q(P) = (1 + tr(P - I))^Q - 1`, and the gap functional of the positive-gap
estimate, `𝔤_Q(P) = ‖P‖_op^{Q-1}tr(P - I) + (tr(P - I))^Q`.  The comparison
between the gap functional and the mean penalty says the two are comparable with
constants depending only on `Q`, and the paragraph proving it reduces the
comparison to the scalar sandwich `x + x^Q ≤ 𝔤_Q(P) ≤ (1 + x)^{Q-1}x + x^Q`,
valid because
`1 ≤ ‖P‖_op ≤ 1 + x` for `x = tr(P - I)`.

That scalar comparability is proved here, with the explicit constant `2^Q`, and
so is the spectral bound `‖P‖_op ≤ 1 + tr(P - I)` that the transport also uses
on its own when it counts the inherited rows: a block above the identity is
below `(1 + tr(P - I))I`, because the positive matrix `P - I` is below its own
trace.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

/-! ## The scalar comparability -/

/-- **The upper half of the comparison between the gap functional and the mean
penalty.**  The larger side of the scalar sandwich is at most twice the gain:
the pure power is below the mixed one, and the mixed one is the difference of
two consecutive powers of `1 + x`, the smaller of which is at least one. -/
theorem gap_upper_scalar {Q x : ℝ} (hQ : 1 ≤ Q) (hx : 0 ≤ x) :
    (1 + x) ^ (Q - 1) * x + x ^ Q ≤ 2 * ((1 + x) ^ Q - 1) := by
  have hQ1 : (0 : ℝ) ≤ Q - 1 := by linarith only [hQ]
  have hbase : (1 : ℝ) ≤ 1 + x := by linarith only [hx]
  have hone : (1 : ℝ) ≤ (1 + x) ^ (Q - 1) := by
    have := Real.rpow_le_rpow zero_le_one hbase hQ1
    rwa [Real.one_rpow] at this
  -- the mixed term is the difference of two consecutive powers
  have hposb : (0 : ℝ) < 1 + x := by linarith only [hx]
  have hmixed : (1 + x) ^ (Q - 1) * x = (1 + x) ^ Q - (1 + x) ^ (Q - 1) := by
    have hsplit : (1 + x) ^ (Q - 1) * (1 + x) ^ (1 : ℝ) = (1 + x) ^ Q := by
      rw [← Real.rpow_add hposb]
      norm_num
    rw [Real.rpow_one] at hsplit
    rw [← hsplit]
    ring
  -- the pure power is below the mixed one
  have hpure : x ^ Q ≤ (1 + x) ^ (Q - 1) * x := by
    rcases eq_or_lt_of_le hx with hzero | hpos
    · rw [← hzero, mul_zero, Real.zero_rpow (by linarith only [hQ])]
    · have hxq : x ^ (Q - 1) * x ^ (1 : ℝ) = x ^ Q := by
        rw [← Real.rpow_add hpos]
        norm_num
      rw [Real.rpow_one] at hxq
      rw [← hxq]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hx (by linarith only [hx]) hQ1) hx
  rw [hmixed] at hpure ⊢
  linarith only [hpure, hone]

/-- **The lower half of the comparison between the gap functional and the mean
penalty.**  The gain is at most `2^Q` times the smaller side of the scalar
sandwich.  Below one the gain is
linear in `x` by convexity; above one the argument `1 + x` is at most `2x`. -/
theorem gap_lower_scalar {Q x : ℝ} (hQ : 1 ≤ Q) (hx : 0 ≤ x) :
    (1 + x) ^ Q - 1 ≤ 2 ^ Q * (x + x ^ Q) := by
  have hQ0 : (0 : ℝ) ≤ Q := by linarith only [hQ]
  have hxq : 0 ≤ x ^ Q := Real.rpow_nonneg hx Q
  have htwo : (2 : ℝ) ≤ 2 ^ Q :=
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ 2 ^ Q := Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr hQ
  rcases le_or_gt x 1 with hle | hgt
  · have hcvx := rpow_sub_one_le_div_mul (Q := Q) hQ hx hle one_pos
    rw [div_one] at hcvx
    have hpow : (1 + (1 : ℝ)) ^ Q - 1 ≤ 2 ^ Q := by
      have : ((1 : ℝ) + 1) ^ Q = 2 ^ Q := by norm_num
      rw [this]
      linarith only [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) Q]
    calc (1 + x) ^ Q - 1 ≤ x * ((1 + (1 : ℝ)) ^ Q - 1) := hcvx
      _ ≤ x * 2 ^ Q := mul_le_mul_of_nonneg_left hpow hx
      _ ≤ 2 ^ Q * (x + x ^ Q) := by nlinarith only [hxq, hx, htwo]
  · have hbound : (1 + x) ^ Q ≤ 2 ^ Q * x ^ Q := by
      have h2x : (1 + x) ≤ 2 * x := by linarith only [hgt]
      have := Real.rpow_le_rpow (by linarith only [hx]) h2x hQ0
      rwa [Real.mul_rpow (by norm_num) hx] at this
    have hxnn : 0 ≤ 2 ^ Q * x := by positivity
    nlinarith only [hbound, hxnn]

/-! ## The spectral size of a block above the identity -/

section Blocks

variable {d : ℕ}

/-- **`‖P‖_op ≤ 1 + tr(P - I)`.**  The step the transport uses when it counts
the inherited rows: the positive matrix `P - I` lies below its own trace times
the identity, so `P` lies below `(1 + tr(P - I))I`. -/
theorem norm_le_one_add_trace_gap {Pm : FullBlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ Pm) :
    ‖Pm‖ ≤ 1 + (Matrix.trace Pm - 2 * (d : ℝ)) := by
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  have hgapps : (Pm - 1).PosSemidef := Matrix.le_iff.mp hPm
  have hgaptr : Matrix.trace (Pm - 1) = Matrix.trace Pm - 2 * (d : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, hcard]
  have hgap0 : 0 ≤ Matrix.trace Pm - 2 * (d : ℝ) := by
    have := hgapps.trace_nonneg
    rwa [hgaptr] at this
  have hone : (0 : FullBlockMat d) ≤ 1 := by
    refine Matrix.le_iff.mpr ?_
    simpa using (Matrix.PosSemidef.one : (1 : FullBlockMat d).PosSemidef)
  have hPps : Pm.PosSemidef := by
    have h0 := Matrix.le_iff.mp (hone.trans hPm)
    simpa using h0
  have hstep : Pm ≤ (1 + (Matrix.trace Pm - 2 * (d : ℝ))) • (1 : FullBlockMat d) := by
    have hle := Recurrence.le_trace_smul_one hgapps
    rw [hgaptr] at hle
    refine Matrix.le_iff.mpr ?_
    have hrw : (1 + (Matrix.trace Pm - 2 * (d : ℝ))) • (1 : FullBlockMat d) - Pm =
        (Matrix.trace Pm - 2 * (d : ℝ)) • (1 : FullBlockMat d) - (Pm - 1) := by
      rw [add_smul, one_smul]
      abel
    rw [hrw]
    exact Matrix.le_iff.mp hle
  exact norm_le_of_le_smul_one hPps (by linarith only [hgap0]) hstep

end Blocks

end

end Transport
end HighContrast
end Homogenization
