/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.DeterminantLoss
import HCPoly.Setup.TransportObjects

/-!
# The determinant account of the short test

The short test of `p.successful.short.bridge` reads one determinant
inequality, `Ξ_u^q ≤ (1 + δ_short)Ξ_{u+2ℓ₀}^q`, and the proof turns it into two
deterministic statements about the annealed blocks of the old grid.

The first is monotonicity of the determinant root along the mean order: the
means decrease with the scale, so their determinants and hence their roots
decrease with them, and the short test therefore also bounds the loss
`e^{σ_q(u,n)} = Ξ_u^q/Ξ_n^q` at the intermediate scale `n`.

The second is the normalization display: the determinant-loss comparison
`e.global.selection.metric.loss` applied to the mean order turns the ratio of
the determinant roots into a Loewner dilation, so `E_u^q ≼ (Ξ_u^q/Ξ_{t₀}^q)^dF`
and the short test then puts the dilation below `(1 + δ_short)^d`.

Both statements are about a pair of positive definite doubled blocks and a
scalar; no law, grid or window enters.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The determinant root along the mean order -/

/-- The determinant root of a doubled block is positive. -/
theorem detRoot_pos {A : BlockMat d} (hA : (toFullBlockMat A).PosDef) :
    0 < detRoot d A :=
  Real.rpow_pos_of_pos hA.det_pos _

/-- **The determinant root is monotone for the Loewner order.**  This is the
monotonicity of `Ξ_j^q` in the scale, read through the mean order. -/
theorem detRoot_le_of_blockMatLoewnerLE {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hB : (toFullBlockMat B).PosDef)
    (h : toFullBlockMat A ≤ toFullBlockMat B) : detRoot d A ≤ detRoot d B :=
  Real.rpow_le_rpow hA.det_pos.le (det_le_det_of_le hA hB h) (by positivity)

/-- **The determinant loss at the intermediate scale.**  If the terminal block
sits below the intermediate one, the short test at the terminal scale also
bounds the loss at the intermediate scale. -/
theorem detRoot_le_of_short_test {Eu En Et : BlockMat d}
    (hEn : (toFullBlockMat En).PosDef) (hEt : (toFullBlockMat Et).PosDef)
    (hmono : toFullBlockMat Et ≤ toFullBlockMat En) {delta : ℝ} (hdelta : 0 ≤ delta)
    (htest : detRoot d Eu ≤ (1 + delta) * detRoot d Et) :
    detRoot d Eu ≤ (1 + delta) * detRoot d En := by
  have hstep := detRoot_le_of_blockMatLoewnerLE hEt hEn hmono
  have hmul := mul_le_mul_of_nonneg_left hstep (by linarith only [hdelta] : (0 : ℝ) ≤ 1 + delta)
  exact htest.trans hmul

/-! ## The normalization display -/

/-- The `d`-th power of the ratio of the two determinant roots is the ratio of
the determinants. -/
theorem detRoot_div_pow (hd : d ≠ 0) {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hB : (toFullBlockMat B).PosDef) :
    (detRoot d A / detRoot d B) ^ d =
      (toFullBlockMat A).det / (toFullBlockMat B).det := by
  have hdiv : (0 : ℝ) ≤ (toFullBlockMat A).det / (toFullBlockMat B).det :=
    (div_pos hA.det_pos hB.det_pos).le
  rw [detRoot, detRoot, ← Real.div_rpow hA.det_pos.le hB.det_pos.le]
  exact Real.rpow_inv_natCast_pow hdiv hd

/-- **The normalization display of the short test.**  For a pair of positive
definite doubled blocks ordered by the mean order, the determinant-loss
comparison turns the ratio of the determinant roots into a Loewner dilation, and
the short test bounds that dilation by `(1 + δ_short)^d`. -/
theorem normalization_of_short_test (hd : d ≠ 0) {Eu Et : BlockMat d}
    (hEu : (toFullBlockMat Eu).PosDef) (hEt : (toFullBlockMat Et).PosDef)
    (hmono : toFullBlockMat Et ≤ toFullBlockMat Eu) {delta : ℝ}
    (htest : detRoot d Eu ≤ (1 + delta) * detRoot d Et) :
    toFullBlockMat Eu ≤ ((1 + delta) ^ d) • toFullBlockMat Et := by
  have hEtroot : 0 < detRoot d Et := detRoot_pos hEt
  have hratio : detRoot d Eu / detRoot d Et ≤ 1 + delta := by
    rw [div_le_iff₀ hEtroot]
    exact htest
  have hnn : 0 ≤ detRoot d Eu / detRoot d Et :=
    div_nonneg (detRoot_pos hEu).le hEtroot.le
  have hpow : (toFullBlockMat Eu).det / (toFullBlockMat Et).det ≤ (1 + delta) ^ d := by
    rw [← detRoot_div_pow hd hEu hEt]
    exact pow_le_pow_left₀ hnn hratio d
  have hstep : toFullBlockMat Eu ≤
      ((toFullBlockMat Eu).det / (toFullBlockMat Et).det) • toFullBlockMat Et :=
    le_det_div_smul hEu hEt hmono
  refine hstep.trans (Matrix.le_iff.mpr ?_)
  have hrw : ((1 + delta) ^ d) • toFullBlockMat Et -
      ((toFullBlockMat Eu).det / (toFullBlockMat Et).det) • toFullBlockMat Et =
      ((1 + delta) ^ d - (toFullBlockMat Eu).det / (toFullBlockMat Et).det) •
        toFullBlockMat Et := by
    rw [sub_smul]
  rw [hrw]
  exact hEt.posSemidef.smul (by linarith only [hpow])

end

end ShortHop
end HighContrast
end Homogenization
