/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.PositiveGap
import HCPoly.Provider.Transport.GapComparison
import HCPoly.Geometry.SizeAlignment

/-!
# The two gain functions on blocks above the identity

The transport carries two gain functions on a doubled block `P ≥ I`: the
fixed-grid section's `𝔥_Q(P) = (1 + tr(P - I))^Q - 1` and the transport's
gap functional `𝔤_Q(P) = ‖P‖_op^{Q-1}tr(P - I) + (tr(P - I))^Q` of the
positive-gap estimate.  The comparison between the gap functional and the mean
penalty asserts that the two are comparable with
constants depending on `Q` alone, and the paragraph proving it reduces the
comparison to the scalar sandwich `x + x^Q ≤ 𝔤_Q(P) ≤ (1 + x)^{Q-1}x + x^Q` at
`x = tr(P - I)`, valid because `1 ≤ ‖P‖_op ≤ 1 + x`.

The two scalar halves of that sandwich are already available; what is proved
here is the passage from them to the blocks the display is written for.  It
turns on one identification.  The setup layer measures a block by the Loewner
size `|H| = inf{t ≥ 0 : -tI ≤ H ≤ tI}`, an infimum; the operator norm of the
flattened matrix is the same number, because the relative size against a
positive reference is the least scalar Loewner bound, and the reference here is
the identity, whose inverse square root is the identity.  Once the two agree,
the upper half of the comparison is the spectral bound `‖P‖_op ≤ 1 + tr(P - I)`
raised to the power `Q - 1`, and the lower half is `1 ≤ ‖P‖_op`, which follows
from the trace of the Loewner bound `P ≤ ‖P‖_op I` in `2d` dimensions.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The Loewner size against the identity is the spectral norm -/

/-- The identity is its own positive semidefinite square root. -/
private theorem matSqrt_one' {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (1 : Matrix n n ℝ) = 1 :=
  matSqrt_eq Matrix.PosSemidef.one Matrix.PosSemidef.one (by simp)

/-- **The operator size of a positive block is the spectral norm of its
flattening.**  The Loewner size `|H|` is an infimum over scalar sandwiches and
the spectral norm is a norm; they agree because the relative size against a
positive reference is the least scalar Loewner bound, and at the identity
reference the normalizing square roots are the identity. -/
theorem blockOpSize_eq_norm {H : BlockMat d} (hH : (toFullBlockMat H).PosSemidef) :
    blockOpSize H = ‖toFullBlockMat H‖ := by
  have hIsym : IsSymmetricBlockMat (Book.Ch02.blockIdentity d) := by
    refine isSymmetricBlockMat_of_posSemidef ?_
    rw [toFullBlockMat_blockIdentity]
    exact Matrix.PosSemidef.one
  have hIpd : Book.Ch02.BlockPosDef (Book.Ch02.blockIdentity d) := by
    refine (blockPosDef_iff_posDef hIsym).mpr ?_
    rw [toFullBlockMat_blockIdentity]
    exact Matrix.PosDef.one
  rw [blockOpSize, blockSize_eq_relSize (isSymmetricBlockMat_of_posSemidef hH) hIsym hIpd hH,
    toFullBlockMat_blockIdentity, relSize_def, inv_one, matSqrt_one', Matrix.one_mul,
    Matrix.mul_one]

/-- A block above the identity is positive definite; the identity is. -/
theorem posDef_of_one_le {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) : (toFullBlockMat Pm).PosDef :=
  posDef_of_posDef_le Matrix.PosDef.one hPm

/-- **`1 ≤ ‖P‖_op` for a block above the identity**, the lower half of the
sandwich `1 ≤ ‖P‖_op ≤ 1 + tr(P - I)` that the comparison between the gap
functional and the mean penalty runs on.  Taking the trace of the Loewner
bound `P ≤ ‖P‖_op I` in `2d` dimensions gives `2d‖P‖_op ≥ tr P ≥ 2d`. -/
theorem one_le_blockOpSize (hd : 0 < d) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) : 1 ≤ blockOpSize Pm := by
  have hPps : (toFullBlockMat Pm).PosSemidef := (posDef_of_one_le hPm).posSemidef
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hdR]
  have htr := Recurrence.two_mul_le_blockTrace_of_one_le hPm
  have hgap := (Matrix.le_iff.mp (le_norm_smul_one hPps)).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hcard, smul_eq_mul] at hgap
  rw [blockOpSize_eq_norm hPps]
  rw [blockTrace] at htr
  refine le_of_mul_le_mul_left ?_ hd0
  rw [mul_one]
  linarith only [hgap, htr]

/-! ## The two gain functions are comparable -/

/-- The trace gap of a block above the identity is nonnegative. -/
theorem zero_le_trace_gap {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    0 ≤ blockTrace Pm - 2 * (d : ℝ) := by
  have h := Recurrence.two_mul_le_blockTrace_of_one_le hPm
  linarith only [h]

/-- The transport gain function is nonnegative on blocks above the identity. -/
theorem zero_le_gapG {Q : ℝ} {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) : 0 ≤ gapG Q Pm := by
  have hx := zero_le_trace_gap hPm
  have hnorm : (0 : ℝ) ≤ blockOpSize Pm ^ (Q - 1) := by
    rw [blockOpSize_eq_norm (posDef_of_one_le hPm).posSemidef]
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hpow : (0 : ℝ) ≤ (blockTrace Pm - 2 * (d : ℝ)) ^ Q := Real.rpow_nonneg hx _
  rw [gapG]
  have hmix := mul_nonneg hnorm hx
  linarith only [hmix, hpow]

/-- **The upper half of the comparison between the gap functional and the mean
penalty**, at the blocks the display is written for: `𝔤_Q(P) ≤ 2𝔥_Q(P)` for
`P ≥ I`.  The spectral size of `P` is at most `1 + tr(P - I)`, so the mixed
summand of `𝔤_Q` is below the
larger side of the scalar sandwich, whose comparison with the gain is the
scalar half. -/
theorem gapG_le_two_mul_frakH {Q : ℝ} (hQ : 1 ≤ Q) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    gapG Q Pm ≤ 2 * frakH Q Pm := by
  have hPps : (toFullBlockMat Pm).PosSemidef := (posDef_of_one_le hPm).posSemidef
  have hx := zero_le_trace_gap hPm
  have hnorm : blockOpSize Pm ≤ 1 + (blockTrace Pm - 2 * (d : ℝ)) := by
    rw [blockOpSize_eq_norm hPps, blockTrace]
    exact norm_le_one_add_trace_gap hPm
  have hpow : blockOpSize Pm ^ (Q - 1) ≤ (1 + (blockTrace Pm - 2 * (d : ℝ))) ^ (Q - 1) :=
    Real.rpow_le_rpow (by rw [blockOpSize_eq_norm hPps]; exact norm_nonneg _) hnorm
      (by linarith only [hQ])
  have hmix := mul_le_mul_of_nonneg_right hpow hx
  have hscal := gap_upper_scalar (Q := Q) (x := blockTrace Pm - 2 * (d : ℝ)) hQ hx
  rw [gapG, frakH]
  linarith only [hmix, hscal]

/-- **The lower half of the comparison between the gap functional and the mean
penalty**, at the blocks the display is written for: `𝔥_Q(P) ≤ 2^Q𝔤_Q(P)` for
`P ≥ I`.  The spectral size of `P` is at least one, so the smaller side of the
scalar sandwich is below
`𝔤_Q(P)`, and its comparison with the gain is the scalar half. -/
theorem frakH_le_rpow_mul_gapG (hd : 0 < d) {Q : ℝ} (hQ : 1 ≤ Q) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    frakH Q Pm ≤ 2 ^ Q * gapG Q Pm := by
  have hx := zero_le_trace_gap hPm
  have hone : (1 : ℝ) ≤ blockOpSize Pm ^ (Q - 1) :=
    Real.one_le_rpow (one_le_blockOpSize hd hPm) (by linarith only [hQ])
  have hmix : blockTrace Pm - 2 * (d : ℝ) ≤
      blockOpSize Pm ^ (Q - 1) * (blockTrace Pm - 2 * (d : ℝ)) :=
    le_mul_of_one_le_left hx hone
  have hscal := gap_lower_scalar (Q := Q) (x := blockTrace Pm - 2 * (d : ℝ)) hQ hx
  have h2 : (0 : ℝ) ≤ 2 ^ Q := Real.rpow_nonneg (by norm_num) _
  have hprod : (0 : ℝ) ≤ 2 ^ Q * (blockOpSize Pm ^ (Q - 1) * (blockTrace Pm - 2 * (d : ℝ)) -
      (blockTrace Pm - 2 * (d : ℝ))) := mul_nonneg h2 (by linarith only [hmix])
  rw [gapG, frakH]
  linarith only [hscal, hprod]

end

end Transport
end HighContrast
end Homogenization
