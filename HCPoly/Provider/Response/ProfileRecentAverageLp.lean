/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentAverageMean
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The probabilistic one-scale averaged-defect bound

Positivity bounds the scalar averaged defect by its trace.  The expectation
identity for that trace and the nonlinear gain inequality then give the exact
`L²` bound at one recent scale.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The square root of the scalar averaged defect is a.e. measurable. -/
theorem aemeasurable_sqrt_diagonalWeakAverageDefect [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    {k t : ℤ} (hlk : l ≤ k) (hkt : k ≤ t)
    (hintk : HasFiniteAdaptedMean P q k)
    (hintt : HasFiniteAdaptedMean P q t) :
    AEMeasurable (fun a ↦ Real.sqrt
      (blockSize
        (diagonalWeakAverageDefect q k t (adaptedMean P q t) a)
        (blockIdentity d))) P := by
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t hintt
  have hDint := integrable_toFullBlockMat_diagonalWeakAverageDefect
    hq hP hgrid hlk hkt hintk hintt
  have hnormMeas : AEMeasurable (fun a ↦
      ‖toFullBlockMat
        (diagonalWeakAverageDefect q k t (adaptedMean P q t) a)‖) P :=
    hDint.aestronglyMeasurable.norm.aemeasurable
  have hsizeMeas : AEMeasurable (fun a ↦
      blockSize
        (diagonalWeakAverageDefect q k t (adaptedMean P q t) a)
        (blockIdentity d)) P := by
    refine hnormMeas.congr (Filter.Eventually.of_forall fun a ↦ ?_)
    exact (Transport.blockOpSize_eq_norm
      (posSemidef_diagonalWeakAverageDefect hq hkt
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt a)).symm
  exact hsizeMeas.sqrt

/-- At one recent scale, the `L²` norm of the square-root averaged defect is
bounded by the `1/(2Q)`-th power of the nonlinear gain. -/
theorem eLpNorm_sqrt_diagonalWeakAverageDefect_le_frakH [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    {k t : ℤ} (hlk : l ≤ k) (hkt : k ≤ t)
    {Q : ℝ} (hQ : 1 ≤ Q)
    (hintk : HasFiniteAdaptedMean P q k)
    (hintt : HasFiniteAdaptedMean P q t) :
    eLpNorm (fun a ↦ Real.sqrt
        (blockSize
          (diagonalWeakAverageDefect q k t (adaptedMean P q t) a)
          (blockIdentity d))) 2 P ≤
      ENNReal.ofReal
        (frakH Q (relMean P q k t) ^ (1 / (2 * Q))) := by
  let D : CoeffSpace d → BlockMat d := fun a ↦
    diagonalWeakAverageDefect q k t (adaptedMean P q t) a
  let X : CoeffSpace d → ℝ := fun a ↦ blockSize (D a) (blockIdentity d)
  let T : CoeffSpace d → ℝ := fun a ↦ blockTrace (D a)
  let gap : ℝ := blockTrace (relMean P q k t) - 2 * (d : ℝ)
  let gain : ℝ := frakH Q (relMean P q k t)
  have hEts : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t hintt
  have hDpos : ∀ a, (toFullBlockMat (D a)).PosSemidef := fun a ↦
    posSemidef_diagonalWeakAverageDefect hq hkt hEts hEt a
  have hX0 : ∀ a, 0 ≤ X a := fun a ↦
    blockSize_diagonalWeakAverageDefect_nonneg hq hkt hEts hEt a
  have hT0 : ∀ a, 0 ≤ T a := fun a ↦ (hDpos a).trace_nonneg
  have hXT : ∀ a, X a ≤ T a := fun a ↦
    blockSize_blockIdentity_le_blockTrace_of_posSemidef (hDpos a)
  have hDint : Integrable (fun a ↦ toFullBlockMat (D a)) P := by
    simpa only [D] using
      integrable_toFullBlockMat_diagonalWeakAverageDefect
        hq hP hgrid hlk hkt hintk hintt
  have hDmean : ∫ a, blockTrace (D a) ∂P = gap := by
    simpa only [D, gap] using
      integral_blockTrace_diagonalWeakAverageDefect_eq
        hq hP hgrid hlk hkt hintk hintt
  have hTone : eLpNorm T 1 P = ENNReal.ofReal gap := by
    exact Recurrence.eLpNorm_blockTrace_eq_ofReal hDpos hDint hDmean
  have hXone : eLpNorm X 1 P ≤ ENNReal.ofReal gap := by
    calc
      eLpNorm X 1 P ≤ eLpNorm T 1 P := eLpNorm_mono fun a ↦ by
        rw [Real.norm_of_nonneg (hX0 a), Real.norm_of_nonneg (hT0 a)]
        exact hXT a
      _ = ENNReal.ofReal gap := hTone
  have hEtfull : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    posDef_toFullBlockMat hEts hEt
  have hmean : toFullBlockMat (adaptedMean P q t) ≤
      toFullBlockMat (adaptedMean P q k) :=
    Recurrence.toFullBlockMat_adaptedMean_le hP hgrid hlk hkt hintk hintt
  have hIP : (1 : FullBlockMat d) ≤ toFullBlockMat (relMean P q k t) := by
    rw [Recurrence.toFullBlockMat_relMean]
    exact Recurrence.one_le_normalize hEtfull hmean
  have hgap0 : 0 ≤ gap := by
    exact Transport.zero_le_trace_gap hIP
  have hgain0 : 0 ≤ gain :=
    frakH_nonneg_of_one_le (by linarith only [hQ]) hIP
  have hgapLe : gap ≤ gain ^ Q⁻¹ :=
    traceGap_le_frakH_rpow_inv hQ hgap0
  have hinvQ0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (by linarith only [hQ])
  have hsqrtNorm : eLpNorm (fun a ↦ Real.sqrt (X a)) 2 P =
      eLpNorm X 1 P ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_norm_rpow (p := (2 : ℝ≥0∞)) (μ := P)
      (q := (1 / 2 : ℝ)) X (by norm_num)
    simpa only [Real.sqrt_eq_rpow, Real.norm_of_nonneg (hX0 _),
      ENNReal.ofReal_ofNat,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one] using h
  have hexp : Q⁻¹ * (1 / 2 : ℝ) = 1 / (2 * Q) := by
    have hQne : Q ≠ 0 := by linarith only [hQ]
    field_simp [hQne]
  change eLpNorm (fun a ↦ Real.sqrt (X a)) 2 P ≤
    ENNReal.ofReal (gain ^ (1 / (2 * Q)))
  calc
    eLpNorm (fun a ↦ Real.sqrt (X a)) 2 P =
        eLpNorm X 1 P ^ (1 / 2 : ℝ) := hsqrtNorm
    _ ≤ ENNReal.ofReal gap ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hXone (by norm_num)
    _ ≤ ENNReal.ofReal (gain ^ Q⁻¹) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hgapLe) (by norm_num)
    _ = ENNReal.ofReal (gain ^ (1 / (2 * Q))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hgain0 _)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply congrArg ENNReal.ofReal
      rw [← Real.rpow_mul hgain0, hexp]

end

end Homogenization.HighContrast.Response
