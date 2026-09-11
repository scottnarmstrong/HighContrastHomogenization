/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Annealed.SchattenDefinedness
import HCPoly.Geometry.SizeAlignment
import HCPoly.Provider.Recurrence.PositiveGapClosure

/-!
# From the two mean comparisons to the near isometry

The successful short test of `p.successful.short.bridge` reads the
two mean comparisons `e.bridge.upper.comparison` at the
intermediate scale and turns them into the near isometry
`e.successful.short.near`, normalized once and for all by
the terminal block of the old grid.

The lower comparison is already normalized by that block, so it gives the lower
half directly.  The upper comparison is normalized by the intermediate block of
the old grid, so the proof passes through the mean order and the normalization
display: the intermediate block sits below the entry block, which sits below a
dilation of the terminal block, and the two factors multiply.  The pair of
factors is exactly what the bridge-error envelope of the ordered choice
measures, so a single bound on that envelope closes both halves.

Everything here is Loewner algebra on four doubled blocks and four scalars.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## Dilations of a positive semidefinite block -/

/-- A dilation of a positive semidefinite block is monotone in the scalar. -/
theorem smul_le_smul_right_of_le {c c' : ℝ} (h : c ≤ c') {T : FullBlockMat d}
    (hT : T.PosSemidef) : c • T ≤ c' • T := by
  refine Matrix.le_iff.mpr ?_
  rw [show c' • T - c • T = (c' - c) • T by rw [sub_smul]]
  exact hT.smul (by linarith only [h])

/-! ## The two halves of the near isometry -/

/-- **The lower half.**  The lower mean comparison is already normalized by the
terminal block of the old grid, so it puts the new intermediate block above
`(1 - ε_-)` times that block; the bridge-error bound then replaces `ε_-` by the
near-isometry allowance. -/
theorem lower_nearIsometry {Enew Et : BlockMat d} (hEtpsd : (toFullBlockMat Et).PosSemidef)
    {epsMinus etaX : ℝ} (hem : epsMinus ≤ etaX)
    (hlower : toFullBlockMat (blockScale (-epsMinus) Et) ≤
      toFullBlockMat (blockSub Enew Et)) :
    ((1 - etaX) : ℝ) • toFullBlockMat Et ≤ toFullBlockMat Enew := by
  rw [toFullBlockMat_blockScale, Recurrence.toFullBlockMat_blockSub] at hlower
  have hstep : ((1 - epsMinus) : ℝ) • toFullBlockMat Et ≤ toFullBlockMat Enew := by
    have hrw : ((1 - epsMinus) : ℝ) • toFullBlockMat Et =
        toFullBlockMat Et + (-epsMinus) • toFullBlockMat Et := by
      rw [neg_smul, sub_smul, one_smul]
      abel
    rw [hrw, add_comm, ← le_sub_iff_add_le]
    exact hlower
  exact (smul_le_smul_right_of_le (by linarith only [hem]) hEtpsd).trans hstep

/-- **The upper half.**  The upper mean comparison is normalized by the
intermediate block of the old grid; the mean order and the normalization
display move that normalization to the terminal block, and the two factors
`(1 + ε_+)` and `(1 + δ_short)^d` multiply into the bridge-error envelope. -/
theorem upper_nearIsometry {Enew Eu En Et : BlockMat d}
    (hEtpsd : (toFullBlockMat Et).PosSemidef)
    {epsPlus delta etaX : ℝ} (hep : 0 ≤ epsPlus)
    (hbr : (1 + epsPlus) * (1 + delta) ^ d - 1 ≤ etaX)
    (hupper : toFullBlockMat (blockSub Enew Eu) ≤
      toFullBlockMat (blockScale epsPlus En))
    (hmono : toFullBlockMat En ≤ toFullBlockMat Eu)
    (hnorm : toFullBlockMat Eu ≤ ((1 + delta) ^ d) • toFullBlockMat Et) :
    toFullBlockMat Enew ≤ ((1 + etaX) : ℝ) • toFullBlockMat Et := by
  rw [toFullBlockMat_blockScale, Recurrence.toFullBlockMat_blockSub] at hupper
  -- the intermediate block is absorbed into the entry block
  have hstep₁ : toFullBlockMat Enew ≤ ((1 + epsPlus) : ℝ) • toFullBlockMat Eu := by
    have hsm : epsPlus • toFullBlockMat En ≤ epsPlus • toFullBlockMat Eu :=
      smul_le_smul_of_le hep hmono
    have hrw : ((1 + epsPlus) : ℝ) • toFullBlockMat Eu =
        toFullBlockMat Eu + epsPlus • toFullBlockMat Eu := by
      rw [add_smul, one_smul]
    rw [hrw, ← sub_le_iff_le_add']
    exact hupper.trans hsm
  -- the entry block is absorbed into the terminal block
  have hstep₂ : ((1 + epsPlus) : ℝ) • toFullBlockMat Eu ≤
      ((1 + epsPlus) * (1 + delta) ^ d : ℝ) • toFullBlockMat Et := by
    have h := smul_le_smul_of_le (by linarith only [hep] : (0 : ℝ) ≤ 1 + epsPlus) hnorm
    rwa [smul_smul] at h
  exact (hstep₁.trans hstep₂).trans
    (smul_le_smul_right_of_le (by linarith only [hbr]) hEtpsd)

/-- **The near isometry of the short test.**  Both halves at once, in the
structural dialect of the doubled block, from the two mean comparisons, the
mean order, the normalization display and a single bound on the bridge-error
envelope. -/
theorem nearIsometry_of_comparisons {Enew Eu En Et : BlockMat d}
    (hEnew : IsSymmetricBlockMat Enew) (hEu : IsSymmetricBlockMat Eu)
    (hEn : IsSymmetricBlockMat En) (hEt : IsSymmetricBlockMat Et)
    (hEtpsd : (toFullBlockMat Et).PosSemidef)
    {epsPlus epsMinus delta etaX : ℝ} (hep : 0 ≤ epsPlus)
    (hbr : max epsMinus ((1 + epsPlus) * (1 + delta) ^ d - 1) ≤ etaX)
    (hupper : BlockMatLoewnerLE (blockSub Enew Eu) (blockScale epsPlus En))
    (hlower : BlockMatLoewnerLE (blockScale (-epsMinus) Et) (blockSub Enew Et))
    (hmono : BlockMatLoewnerLE En Eu)
    (hnorm : toFullBlockMat Eu ≤ ((1 + delta) ^ d) • toFullBlockMat Et) :
    BlockMatLoewnerLE (blockScale (1 - etaX) Et) Enew ∧
      BlockMatLoewnerLE Enew (blockScale (1 + etaX) Et) := by
  have hupperF := le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockSub hEnew hEu)
    (isSymmetricBlockMat_blockScale _ hEn) hupper
  have hlowerF := le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockScale _ hEt)
    (isSymmetricBlockMat_blockSub hEnew hEt) hlower
  have hmonoF := le_of_blockMatLoewnerLE hEn hEu hmono
  refine ⟨blockMatLoewnerLE_of_le ?_, blockMatLoewnerLE_of_le ?_⟩
  · rw [toFullBlockMat_blockScale]
    exact lower_nearIsometry hEtpsd (le_trans (le_max_left _ _) hbr) hlowerF
  · rw [toFullBlockMat_blockScale]
    exact upper_nearIsometry hEtpsd hep (le_trans (le_max_right _ _) hbr) hupperF hmonoF hnorm

end

end ShortHop
end HighContrast
end Homogenization
