/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowAlignedSum
import HCPoly.Provider.Response.ProfileMaximumMean
import HCPoly.Provider.Recurrence.MeanOrder

/-!
# Annealed response row above the alignment scale

Stationarity turns every aligned cell at scale `k` into the adapted mean at
that scale.  Positive mean increments are then measured in the terminal
geometry and summed by `ProfileRowAlignedSum`.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem adaptedMean_quadratic_nonneg
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) (s : ℤ)
    (hfin : HasFiniteAdaptedMean P q s) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul (adaptedMean P q s) X) := by
  rw [blockVecDot_blockMatVecMul_eq_dotProduct]
  have hpd := Recurrence.posDef_toFullBlockMat_adaptedMean hq s hfin
  exact hpd.posSemidef.dotProduct_mulVec_nonneg _

/-- The normalized terminal trace of one positive mean increment. -/
private def profileMeanIncrement
    (P : Measure (CoeffSpace d)) (q : Mat d) (s r : ℤ) : ℝ :=
  blockTrace
    (ofFullBlockMat
      ((toFullBlockMat (adaptedMean P q s))⁻¹ *
        toFullBlockMat
          (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r))))

private theorem profileMeanIncrement_nonneg [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} {jStar s r : ℤ} (hq : IsRoundedGrid jStar q)
    (hjr : jStar + 1 ≤ r) (hrs : r ≤ s)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ s →
      HasFiniteAdaptedMean P q k) :
    0 ≤ profileMeanIncrement P q s r := by
  have hjs : jStar ≤ s := by omega
  have hspos := Recurrence.posDef_toFullBlockMat_adaptedMean hq s
    (hfin s hjs le_rfl)
  have horder :
      toFullBlockMat (adaptedMean P q r) ≤
        toFullBlockMat (adaptedMean P q (r - 1)) :=
    Recurrence.toFullBlockMat_adaptedMean_le hstat hq (by omega) (by omega)
      (hfin (r - 1) (by omega) (by omega))
      (hfin r (by omega) hrs)
  have hgap :
      (toFullBlockMat
        (blockSub (adaptedMean P q (r - 1))
          (adaptedMean P q r))).PosSemidef := by
    rw [Recurrence.toFullBlockMat_blockSub]
    exact Matrix.le_iff.mp horder
  rw [profileMeanIncrement, blockTrace, toFullBlockMat_ofFullBlockMat]
  exact PortableHistory.trace_mul_nonneg hspos.inv.posSemidef hgap

private theorem adaptedMean_le_terminal_trace [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} {jStar k s : ℤ} (hq : IsRoundedGrid jStar q)
    (hjk : jStar ≤ k) (hks : k ≤ s)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ s →
      HasFiniteAdaptedMean P q r) :
    BlockMatLoewnerLE (adaptedMean P q k)
      (blockScale
        (1 + ∑ r ∈ Finset.Icc (k + 1) s,
          profileMeanIncrement P q s r)
        (adaptedMean P q s)) := by
  have hjs : jStar ≤ s := hjk.trans hks
  have hspos := Recurrence.posDef_toFullBlockMat_adaptedMean hq s
    (hfin s hjs le_rfl)
  have horder :
      toFullBlockMat (adaptedMean P q s) ≤
        toFullBlockMat (adaptedMean P q k) :=
    Recurrence.toFullBlockMat_adaptedMean_le hstat hq hjk hks
      (hfin k hjk hks) (hfin s hjs le_rfl)
  have hmean := Bridge.matrix_le_terminal_trace_sub hspos horder
  rw [← Recurrence.toFullBlockMat_blockSub,
    trace_mean_sub_eq_sum (P := P) (q := q) hks] at hmean
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  simpa only [profileMeanIncrement] using hmean

private theorem avsum_annealed_quadratic_eq [NeZero d]
    {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} {jStar k s : ℤ} (hq : IsRoundedGrid jStar q)
    (hjk : jStar ≤ k) (hks : k ≤ s)
    (hfin : HasFiniteAdaptedMean P q k) (X : BlockVec d) :
    avsum (alignedIndex q k s) (fun w ↦
        blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellAt q k w)) X)) =
      blockVecDot X (blockMatVecMul (adaptedMean P q k) X) := by
  have hmeas : HasMeasurableCoarseBlock P (adaptedCell q k) :=
    fun α β => (hfin α β).aestronglyMeasurable
  have hcell : ∀ w ∈ alignedIndex q k s,
      blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellAt q k w)) X) =
        blockVecDot X (blockMatVecMul (adaptedMean P q k) X) := by
    intro w _
    rw [Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hstat hq hjk hmeas w]
  calc
    avsum (alignedIndex q k s) (fun w ↦
        blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellAt q k w)) X)) =
      avsum (alignedIndex q k s) (fun _ ↦
        blockVecDot X (blockMatVecMul (adaptedMean P q k) X)) := by
      rw [avsum_eq, avsum_eq]
      congr 1
      exact Finset.sum_congr rfl hcell
    _ = _ := avsum_const
      (alignedIndex_nonempty (Recurrence.posDef_of_isRoundedGrid hq) hks) _

/-- The primal annealed row from the alignment scale through `s`. -/
theorem profilePrimalAlignedQuadraticRow_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} {jStar : ℤ} (hq : IsRoundedGrid jStar q)
    {rhoDr : ℝ} (hrho : rhoDr < 3 / 2)
    {s : ℤ} (hjs : jStar ≤ s)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ s →
      HasFiniteAdaptedMean P q k) (X : BlockVec d) :
    ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
        avsum (alignedIndex q k s) (fun w ↦
          blockVecDot X
            (blockMatVecMul (annealedBlock P (adaptedCellAt q k w)) X)) ≤
      (1 + linearDrift P rhoDr q jStar s) /
          (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) *
        blockVecDot X (blockMatVecMul (adaptedMean P q s) X) := by
  let inc : ℤ → ℝ := profileMeanIncrement P q s
  have hinc : ∀ r ∈ Finset.Icc (jStar + 1) s, 0 ≤ inc r := by
    intro r hr
    exact profileMeanIncrement_nonneg hstat hq
      (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 hfin
  have hcoef := profileRow_weighted_one_add_tail_le hrho inc hinc
  have hDrift :
      ∑ r ∈ Finset.Icc (jStar + 1) s,
          (3 : ℝ) ^ (-rhoDr * ((s : ℝ) - (r : ℝ))) * inc r =
        linearDrift P rhoDr q jStar s := by
    rfl
  rw [hDrift] at hcoef
  have hsquad : 0 ≤
      blockVecDot X (blockMatVecMul (adaptedMean P q s) X) :=
    adaptedMean_quadratic_nonneg hq s (hfin s hjs le_rfl) X
  have hterm : ∀ k ∈ Finset.Icc jStar s,
      avsum (alignedIndex q k s) (fun w ↦
          blockVecDot X
            (blockMatVecMul (annealedBlock P (adaptedCellAt q k w)) X)) ≤
        (1 + ∑ r ∈ Finset.Icc (k + 1) s, inc r) *
          blockVecDot X (blockMatVecMul (adaptedMean P q s) X) := by
    intro k hk
    have hkr := Finset.mem_Icc.mp hk
    rw [avsum_annealed_quadratic_eq hstat hq hkr.1 hkr.2
      (hfin k hkr.1 hkr.2) X]
    have h := adaptedMean_le_terminal_trace hstat hq hkr.1 hkr.2 hfin X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h
    linarith only [h]
  calc
    ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
        avsum (alignedIndex q k s) (fun w ↦
          blockVecDot X
            (blockMatVecMul (annealedBlock P (adaptedCellAt q k w)) X)) ≤
      ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
        ((1 + ∑ r ∈ Finset.Icc (k + 1) s, inc r) *
          blockVecDot X (blockMatVecMul (adaptedMean P q s) X)) := by
      exact Finset.sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_left (hterm k hk)
          (Real.rpow_nonneg (by norm_num) _)
    _ = (∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
          (1 + ∑ r ∈ Finset.Icc (k + 1) s, inc r)) *
        blockVecDot X (blockMatVecMul (adaptedMean P q s) X) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hsquad

end

end Homogenization.HighContrast.Response
