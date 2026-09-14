/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentCellLp
import HCPoly.Provider.Recurrence.PositiveGapClosure

/-!
# The mean of the recent averaged defect

The aligned response average is integrable and has the child-scale adapted
mean.  Normalization by the terminal adapted mean therefore identifies the
expected trace of the recent averaged defect with the trace gap of the
relative mean.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The spectral size of a positive doubled block is bounded by its trace. -/
theorem blockSize_blockIdentity_le_blockTrace_of_posSemidef
    {D : BlockMat d} (hD : (toFullBlockMat D).PosSemidef) :
    blockSize D (blockIdentity d) ≤ blockTrace D := by
  change blockOpSize D ≤ blockTrace D
  rw [Transport.blockOpSize_eq_norm hD]
  exact norm_le_of_le_smul_one hD hD.trace_nonneg (Recurrence.le_trace_smul_one hD)

/-- The recent averaged defect is Bochner integrable. -/
theorem integrable_toFullBlockMat_diagonalWeakAverageDefect [NeZero d]
    {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} (hq : q.PosDef)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    {k t : ℤ} (hlk : l ≤ k) (hkt : k ≤ t)
    (hintk : HasFiniteAdaptedMean P q k)
    (hintt : HasFiniteAdaptedMean P q t) :
    Integrable (fun a ↦ toFullBlockMat
      (diagonalWeakAverageDefect q k t (adaptedMean P q t) a)) P := by
  let Z := alignedIndex q k t
  let G : CoeffSpace d → BlockMat d := fun a ↦
    ofFullBlockMat ((Z.card : ℝ)⁻¹ •
      ∑ w ∈ Z, toFullBlockMat (adaptedResponse q k w a))
  have hGfull : ∀ a, toFullBlockMat (G a) =
      (Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (adaptedResponse q k w a) :=
    fun a ↦ toFullBlockMat_ofFullBlockMat _
  have hGint : Integrable (fun a ↦ toFullBlockMat (G a)) P := by
    have hentry : ∀ w ∈ Z, ∀ α β : BlockCoord d,
        Integrable (fun a ↦ toFullBlockMat (adaptedResponse q k w a) α β) P :=
      fun w _ α β ↦ (Recurrence.hasIntegrableCoarseBlock_adaptedCellAt
          hP hgrid hlk hintk w α β).congr
        (_root_.Filter.Eventually.of_forall fun a ↦
          (toFullBlockMat_eq_blockMatEntry (coarseBlock (adaptedCellAt q k w) a) α β).symm)
    simp only [hGfull]
    exact integrable_of_entries fun α β ↦ by
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      exact (integrable_finsetSum Z fun w hw ↦ hentry w hw α β).const_mul _
  have hnormalized :=
    Recurrence.integrable_toFullBlockMat_normalizedBlock_blockSub hintt hGint
  refine hnormalized.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact (toFullBlockMat_diagonalWeakAverageDefect_eq_normalized
    hq hkt (adaptedMean P q t) a).symm

/-- The expected trace of the recent averaged defect is the nonlinear trace
gap of the corresponding relative mean. -/
theorem integral_blockTrace_diagonalWeakAverageDefect_eq [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    {k t : ℤ} (hlk : l ≤ k) (hkt : k ≤ t)
    (hintk : HasFiniteAdaptedMean P q k)
    (hintt : HasFiniteAdaptedMean P q t) :
    ∫ a, blockTrace
        (diagonalWeakAverageDefect q k t (adaptedMean P q t) a) ∂P =
      blockTrace (relMean P q k t) - 2 * (d : ℝ) := by
  let Z := alignedIndex q k t
  let G : CoeffSpace d → BlockMat d := fun a ↦
    ofFullBlockMat ((Z.card : ℝ)⁻¹ •
      ∑ w ∈ Z, toFullBlockMat (adaptedResponse q k w a))
  have hZne : Z.Nonempty := alignedIndex_nonempty hq hkt
  have hGfull : ∀ a, toFullBlockMat (G a) =
      (Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (adaptedResponse q k w a) :=
    fun a ↦ toFullBlockMat_ofFullBlockMat _
  have hGint : Integrable (fun a ↦ toFullBlockMat (G a)) P := by
    have hentry : ∀ w ∈ Z, ∀ α β : BlockCoord d,
        Integrable (fun a ↦ toFullBlockMat (adaptedResponse q k w a) α β) P :=
      fun w _ α β ↦ (Recurrence.hasIntegrableCoarseBlock_adaptedCellAt
          hP hgrid hlk hintk w α β).congr
        (_root_.Filter.Eventually.of_forall fun a ↦
          (toFullBlockMat_eq_blockMatEntry (coarseBlock (adaptedCellAt q k w) a) α β).symm)
    simp only [hGfull]
    exact integrable_of_entries fun α β ↦ by
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      exact (integrable_finsetSum Z fun w hw ↦ hentry w hw α β).const_mul _
  have hGmean : ∫ a, toFullBlockMat (G a) ∂P =
      toFullBlockMat (adaptedMean P q k) := by
    simp only [hGfull]
    simpa only [adaptedResponse] using
      Recurrence.integral_alignedAverage_eq_adaptedMean
        hP hgrid hlk hintk hZne
  have hEt : (toFullBlockMat (adaptedMean P q t)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hgrid t hintt
  calc
    ∫ a, blockTrace
          (diagonalWeakAverageDefect q k t (adaptedMean P q t) a) ∂P =
        ∫ a, blockTrace
          (normalizedBlock
            (blockSub (G a) (coarseBlock (adaptedCell q t) a))
            (adaptedMean P q t)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with a
      exact congrArg Matrix.trace
        (toFullBlockMat_diagonalWeakAverageDefect_eq_normalized
          hq hkt (adaptedMean P q t) a)
    _ = blockTrace (relMean P q k t) - 2 * (d : ℝ) :=
      Recurrence.integral_blockTrace_normalizedBlock_blockSub
        hintt hEt hGint hGmean

end

end Homogenization.HighContrast.Response
