/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentPointwise
import HCPoly.Provider.PortableHistory.CheckpointMoment
import HCPoly.Provider.Transport.NonlinearRow

/-!
# The recent cell sum from a terminal profile

At each recent scale the cell defect is bounded by two copies of the centered
terminal maximum and one nonlinear mean increment.  Summing the exact finite
weights gives the two printed window coefficients.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The nonlinear gain is nonnegative when its block lies above the identity. -/
theorem frakH_nonneg_of_one_le {Q : ℝ} (hQ : 0 ≤ Q) {Pm : BlockMat d}
    (hPm : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) :
    0 ≤ frakH Q Pm :=
  Transport.zero_le_frakH hQ hPm

/-- The centered response of the terminal cell is bounded by `Z_t` on its
finite branch. -/
theorem terminal_centered_le_profileCenteredMaximum_toReal [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax : ℝ} {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (hjt : jStar ≤ t) {a : CoeffSpace d}
    (hEt : BlockPosDef (adaptedMean P q t))
    (htop : profileCenteredMaximum P rhoMax q jStar t a ≠ ⊤) :
    blockSize
        (blockSub (adaptedMean P q t) (coarseBlock (adaptedCell q t) a))
        (adaptedMean P q t) ≤
      (profileCenteredMaximum P rhoMax q jStar t a).toReal := by
  have hEts : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hAts : IsSymmetricBlockMat (coarseBlock (adaptedCell q t) a) :=
    isSymmetricBlockMat_coarseBlock _ a
  have hsize : 0 ≤ blockSize
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t) :=
    PortableHistory.blockSize_nonneg (isSymmetricBlockMat_blockSub hAts hEts) hEts hEt
  have hread := ENNReal.toReal_mono htop
    (PortableHistory.ofReal_blockSize_le_centeredSup hq (rhoMax := rhoMax) hjt a)
  rw [ENNReal.toReal_ofReal hsize] at hread
  rw [blockSize_blockSub_comm hEts hAts hEts hEt]
  exact hread

/-- One recent cell defect is controlled by its centered maximum and nonlinear
mean gain.  The extended-real statement remains valid if the centered maximum
is infinite. -/
theorem ofReal_diagonalWeakCellDefect_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {jStar k t : ℤ} (hjk : jStar ≤ k) (hkt : k ≤ t)
    {Q rhoMax : ℝ} (hQ : 1 ≤ Q) (hrho : 0 ≤ rhoMax)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k))
    (a : CoeffSpace d) :
    ENNReal.ofReal
        (diagonalWeakCellDefect q k t (adaptedMean P q t) a) ≤
      ENNReal.ofReal
          (2 * (3 : ℝ) ^ (rhoMax * ((t : ℝ) - (k : ℝ)))) *
        profileCenteredMaximum P rhoMax q jStar t a +
      ENNReal.ofReal (frakH Q (relMean P q k t) ^ Q⁻¹) := by
  let Z := profileCenteredMaximum P rhoMax q jStar t a
  let R := (3 : ℝ) ^ (rhoMax * ((t : ℝ) - (k : ℝ)))
  let N := frakH Q (relMean P q k t) ^ Q⁻¹
  have hEts : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hEks : IsSymmetricBlockMat (adaptedMean P q k) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q k
  have hAt : IsSymmetricBlockMat (coarseBlock (adaptedCell q t) a) :=
    isSymmetricBlockMat_coarseBlock _ a
  have hgap : (0 : ℝ) ≤ (t : ℝ) - (k : ℝ) := by exact_mod_cast sub_nonneg.mpr hkt
  have hR0 : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hR1 : 1 ≤ R := Real.one_le_rpow (by norm_num)
    (mul_nonneg hrho hgap)
  have hEtfull : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat hEts hEt
  have hmeanFull : toFullBlockMat (adaptedMean P q t) ≤
      toFullBlockMat (adaptedMean P q k) :=
    (blockMatLoewnerLE_iff_le hEts hEks).mp hmean
  have hIP : (1 : FullBlockMat d) ≤ toFullBlockMat (relMean P q k t) := by
    rw [Recurrence.toFullBlockMat_relMean]
    exact Recurrence.one_le_normalize hEtfull hmeanFull
  have hfrak0 : 0 ≤ frakH Q (relMean P q k t) :=
    frakH_nonneg_of_one_le (by linarith only [hQ]) hIP
  have hN0 : 0 ≤ N := Real.rpow_nonneg hfrak0 _
  by_cases htop : Z = ⊤
  · have hcoef : ENNReal.ofReal (2 * R) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    change ENNReal.ofReal
        (diagonalWeakCellDefect q k t (adaptedMean P q t) a) ≤
      ENNReal.ofReal (2 * R) * Z + ENNReal.ofReal N
    rw [htop, ENNReal.mul_top hcoef, top_add]
    exact le_top
  have hcenterTerminal : blockSize
      (blockSub (adaptedMean P q t) (coarseBlock (adaptedCell q t) a))
      (adaptedMean P q t) ≤ Z.toReal := by
    exact terminal_centered_le_profileCenteredMaximum_toReal hq
      (le_trans hjk hkt) hEt htop
  have hmeanRoot : blockSize
      (blockSub (adaptedMean P q k) (adaptedMean P q t))
      (adaptedMean P q t) ≤ N := by
    exact blockSize_adaptedMean_sub_le_frakH hQ hEt hmean
  let B : (Fin d → ℤ) → ℝ := fun w =>
    blockSize
      (blockSub (adaptedResponse q k w a) (coarseBlock (adaptedCell q t) a))
      (adaptedMean P q t)
  have hB0 : ∀ w, 0 ≤ B w := by
    intro w
    exact PortableHistory.blockSize_nonneg
      (isSymmetricBlockMat_blockSub
        (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a) hAt)
      hEts hEt
  have hcell : ∀ w ∈ alignedIndex q k t, B w ≤ 2 * R * Z.toReal + N := by
    intro w hw
    have hw' : adaptedCellCenter q k w ∈ adaptedCell q t := by
      have hset : w ∈ (↑(alignedIndex q k t) : Set (Fin d → ℤ)) := hw
      rwa [coe_alignedIndex hq hkt] at hset
    have hcenter0 : 0 ≤ blockSize
        (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
        (adaptedMean P q t) :=
      PortableHistory.blockSize_nonneg
        (isSymmetricBlockMat_blockSub
          (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a) hEks)
        hEts hEt
    have hcenter := centered_cell_le_profileCenteredMaximum_toReal
      hjk hkt hw' htop hcenter0
    have htri1 := blockSize_blockSub_triangle
      (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a) hEks hAt hEts hEt
    have htri2 := blockSize_blockSub_triangle hEks hEts hAt hEts hEt
    have hZ0 : 0 ≤ Z.toReal := ENNReal.toReal_nonneg
    have hterminal : Z.toReal ≤ R * Z.toReal := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hR1 hZ0
    dsimp only [B]
    calc
      blockSize
          (blockSub (adaptedResponse q k w a) (coarseBlock (adaptedCell q t) a))
          (adaptedMean P q t) ≤
        blockSize
            (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
            (adaptedMean P q t) +
          blockSize
            (blockSub (adaptedMean P q k) (coarseBlock (adaptedCell q t) a))
            (adaptedMean P q t) := htri1
      _ ≤ blockSize
            (blockSub (adaptedResponse q k w a) (adaptedMean P q k))
            (adaptedMean P q t) +
          (blockSize
              (blockSub (adaptedMean P q k) (adaptedMean P q t))
              (adaptedMean P q t) +
            blockSize
              (blockSub (adaptedMean P q t) (coarseBlock (adaptedCell q t) a))
              (adaptedMean P q t)) := add_le_add le_rfl htri2
      _ ≤ R * Z.toReal + (N + R * Z.toReal) :=
        add_le_add hcenter (add_le_add hmeanRoot (hcenterTerminal.trans hterminal))
      _ = 2 * R * Z.toReal + N := by ring
  have hc0 : 0 ≤ 2 * R * Z.toReal + N := by positivity
  have hdefect :
      diagonalWeakCellDefect q k t (adaptedMean P q t) a ≤
        2 * R * Z.toReal + N := by
    rw [diagonalWeakCellDefect]
    have hsq : avsum (alignedIndex q k t) (fun w => B w ^ 2) ≤
        (2 * R * Z.toReal + N) ^ 2 := by
      refine avsum_le_of_forall_le (alignedIndex_nonempty hq hkt) ?_
      intro w hw
      exact pow_le_pow_left₀ (hB0 w) (hcell w hw) 2
    calc
      Real.sqrt (avsum (alignedIndex q k t) (fun w => B w ^ 2)) ≤
          Real.sqrt ((2 * R * Z.toReal + N) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * R * Z.toReal + N := Real.sqrt_sq hc0
  have hcoef0 : 0 ≤ 2 * R := by positivity
  calc
    ENNReal.ofReal
        (diagonalWeakCellDefect q k t (adaptedMean P q t) a) ≤
      ENNReal.ofReal (2 * R * Z.toReal + N) :=
        ENNReal.ofReal_le_ofReal hdefect
    _ = ENNReal.ofReal (2 * R) * Z + ENNReal.ofReal N := by
      rw [ENNReal.ofReal_add (mul_nonneg hcoef0 ENNReal.toReal_nonneg) hN0,
        ENNReal.ofReal_mul hcoef0, ENNReal.ofReal_toReal htop]

end

end Homogenization.HighContrast.Response
