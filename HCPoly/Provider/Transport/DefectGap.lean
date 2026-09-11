/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.GapFunctions
import HCPoly.Provider.Recurrence.PositiveGapClosure

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The two collective defect charges fit inside the upper mean's gap. -/
theorem defect_terms_le_gapG {Q : ℝ} (hQ : 1 ≤ Q) {H K : BlockMat d}
    (hIH : (1 : FullBlockMat d) ≤ toFullBlockMat H)
    (hHK : toFullBlockMat H ≤ toFullBlockMat K) :
    blockOpSize K ^ (Q - 1) * blockTrace (blockSub K H) +
        blockTrace (blockSub K H) ^ Q ≤ gapG Q K := by
  have hIK : (1 : FullBlockMat d) ≤ toFullBlockMat K := hIH.trans hHK
  have hBps : (toFullBlockMat (blockSub K H)).PosSemidef := by
    rw [Recurrence.toFullBlockMat_blockSub]
    exact Matrix.le_iff.mp hHK
  have hB0 : 0 ≤ blockTrace (blockSub K H) := hBps.trace_nonneg
  have hgap0 : 0 ≤ blockTrace K - 2 * (d : ℝ) := zero_le_trace_gap hIK
  have htrH := Recurrence.two_mul_le_blockTrace_of_one_le hIH
  have hBform : blockTrace (blockSub K H) = blockTrace K - blockTrace H := by
    simp only [blockTrace, Recurrence.toFullBlockMat_blockSub, Matrix.trace_sub]
  have hBgap : blockTrace (blockSub K H) ≤ blockTrace K - 2 * (d : ℝ) := by
    rw [hBform]
    linarith only [htrH]
  have hKps : (toFullBlockMat K).PosSemidef := (posDef_of_one_le hIK).posSemidef
  have hcoef0 : 0 ≤ blockOpSize K ^ (Q - 1) := by
    rw [blockOpSize_eq_norm hKps]
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hlin := mul_le_mul_of_nonneg_left hBgap hcoef0
  have hpow := Real.rpow_le_rpow hB0 hBgap (by linarith only [hQ])
  rw [gapG]
  exact add_le_add hlin hpow

end Transport
end HighContrast
end Homogenization
