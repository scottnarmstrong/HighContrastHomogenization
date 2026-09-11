/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredSplit

/-!
# The sup-form inherited engine of the transported centered history

`e.two.grid.old.history.factor` charges the whole inherited content of
the transported centered history — every target level at once — to the centered
history at the checkpoint.  The mechanism is the sentence at 03:1353: "the
terminal weight and max-to-sum give, uniformly in `j`, the root coefficient".
Uniformly in `j` is the whole point: the renormalization envelope
`3^{ρ_max(b-j)}` of a target level cancels against the terminal weight
`3^{-ρ_max(n-j)}` *exactly*, leaving the `j`-free coefficient
`3^{-ρ_max(n-b)}`, and the dimensional entropy enters once, through the single
global family of scale-`b` ancestors, at the max-to-sum step.

The cancellation must happen inside the pathwise supremum.  A level-summed
arrangement — bounding each target level's inherited moment and summing against
the target coefficient — counts every ancestor statistic once per target level
and once per target cell, and the sub-checkpoint levels then diverge like
`3^{d(b-j_*)}`: the fluctuation shared by all the cells of an ancestor must be
paid for once, not once per cell.  This file performs the collapse: the
supremum over all target levels and cells of the weighted inherited parts is
bounded, at every sample, by one `j`-free multiple of the supremum of the
ancestor statistics, whose `Q`-th moment the max-to-sum and stationarity
comparisons behind the row sum inside an ancestor total to the centered
history at the checkpoint times the ancestor count.

The inherited parts themselves are abstract here: the consumer supplies, for
each target level and cell, the pathwise bound of its inherited filling sum by
the row-weight envelope times the supremum of the ancestor statistics — the
scalar-size subadditivity, the per-cell renormalization, and the membership of
each filling cell's statistic in its own ancestor's supremum, which are the
per-cell facts of the row sum inside an ancestor.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The pathwise collapse.**  If every target level and cell carries a
pathwise bound by the envelope `3^{ρ_max(b-j)}` times the supremum of the
ancestor statistics, then the weighted supremum over all target levels and
cells is bounded by the `j`-free coefficient times that same supremum: the
envelope cancels the terminal weight exactly. -/
theorem sup_collapse_le {jStar b n : ℤ} {rhoMax lam CW : ℝ}
    {mem : ℤ → (Fin d → ℤ) → Prop} {u : ℤ → (Fin d → ℤ) → ℝ} {X : ℝ≥0∞}
    (hcell : ∀ j, jStar ≤ j → j ≤ n → ∀ w, mem j w →
      ENNReal.ofReal (u j w) ≤
        ENNReal.ofReal (lam * CW * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ)))) * X) :
    (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ n) (w : Fin d → ℤ) (_ : mem j w),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) * u j w)) ≤
      ENNReal.ofReal (lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) * X := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  refine iSup_le fun j => iSup_le fun hj1 => iSup_le fun hj2 => iSup_le fun w =>
    iSup_le fun hw => ?_
  have hwt : (0 : ℝ) ≤ (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg h3.le _
  calc ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) * u j w)
      = ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ)))) *
          ENNReal.ofReal (u j w) := by
        rw [← ENNReal.ofReal_mul hwt]
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ)))) *
          (ENNReal.ofReal (lam * CW * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ)))) * X) :=
        mul_le_mul' le_rfl (hcell j hj1 hj2 w hw)
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
          (lam * CW * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ))))) * X := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hwt]
    _ = ENNReal.ofReal (lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) * X := by
        refine congrArg₂ (· * ·) (congrArg ENNReal.ofReal ?_) rfl
        rw [show (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
              (lam * CW * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ)))) =
            lam * CW * ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
              (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ)))) from by ring]
        rw [← Real.rpow_add h3]
        ring_nf

/-- **The sup-form inherited engine.**  The `Q`-th moment of the weighted
supremum, over all target levels and cells, of the inherited parts is bounded by
the `j`-free root coefficient raised to the power `Q` times the ancestor count
times the centered history at the checkpoint.

The three steps are the printed ones, in the printed order: the pathwise
collapse against the supremum of the ancestor statistics (the exact
envelope/weight cancellation, uniformly in `j`), the max-to-sum over the global
ancestor family, and the stationarity comparison `E[X_B^Q] ≤ 𝓗_q^cen(b)` of
each ancestor, totalled by the count in the row sum inside an ancestor. -/
theorem sup_inherited_le [NeZero d] {P : Measure (CoeffSpace d)} {l : ℤ} {p q : Mat d}
    {jStar b n : ℤ} {Q rhoMax lam CW Khop : ℝ} {y : Vec d}
    {Zanc : Finset (Fin d → ℤ)} {mem : ℤ → (Fin d → ℤ) → Prop}
    {u : ℤ → (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hd : 1 ≤ d) (hQ : 0 < Q) (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hq : IsRoundedGrid l q) (hlb : l ≤ b) (hbn : b ≤ n)
    (hK : gridRatio q p ≤ Khop)
    (hpdb : Book.Ch02.BlockPosDef (adaptedMean P q b))
    (hZanc : ∀ w ∈ Zanc, (adaptedCellAt q b w ∩ adaptedCellTranslate p n y).Nonempty)
    (hlam : 0 ≤ lam) (hCW : 0 ≤ CW)
    (hcell : ∀ x : CoeffSpace d, ∀ j, jStar ≤ j → j ≤ n → ∀ w, mem j w →
      ENNReal.ofReal (u j w x) ≤
        ENNReal.ofReal (lam * CW * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ)))) *
          ⨆ vB ∈ Zanc, ⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b) (w' : Fin d → ℤ)
              (_ : adaptedCellAt q r w' ⊆ adaptedCellAt q b vB),
            ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
              blockSize (blockSub (adaptedResponse q r w' x) (adaptedMean P q r))
                (adaptedMean P q b))) :
    ∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ n) (w : Fin d → ℤ) (_ : mem j w),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) * u j w x)) ^ Q ∂P ≤
      ENNReal.ofReal ((lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
        (ENNReal.ofReal ((2 + Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((n - b) * (d : ℤ))) *
          centeredHistory P Q rhoMax q jStar b) := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hbsym : IsSymmetricBlockMat (adaptedMean P q b) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q b
  have hcoef0 : (0 : ℝ) ≤ lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ))) :=
    mul_nonneg (mul_nonneg hlam hCW) (Real.rpow_nonneg (by norm_num) _)
  -- the ancestor statistics and their measurability
  set X : (Fin d → ℤ) → CoeffSpace d → ℝ≥0∞ := fun vB x =>
    ⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b) (w' : Fin d → ℤ)
        (_ : adaptedCellAt q r w' ⊆ adaptedCellAt q b vB),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
        blockSize (blockSub (adaptedResponse q r w' x) (adaptedMean P q r))
          (adaptedMean P q b)) with hXdef
  have hbase : ∀ (r : ℤ) (w' : Fin d → ℤ), AEMeasurable (fun x : CoeffSpace d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
        blockSize (blockSub (adaptedResponse q r w' x) (adaptedMean P q r))
          (adaptedMean P q b))) P := by
    intro r w'
    have hmeas := PortableHistory.aemeasurable_blockSize_coarseBlock_sub
      (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hqPD r w')
      (Recurrence.isSymmetricBlockMat_adaptedMean P q r) hbsym hpdb
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hmeas.const_mul _)
  have hmeasQ : ∀ vB : Fin d → ℤ, AEMeasurable (fun x => X vB x ^ Q) P := fun vB =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (AEMeasurable.iSup fun r => AEMeasurable.iSup fun _ => AEMeasurable.iSup fun _ =>
        AEMeasurable.iSup fun w' => AEMeasurable.iSup fun _ => hbase r w')
  -- the pathwise collapse and the max-to-sum
  have hpath : ∀ x : CoeffSpace d,
      (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ n) (w : Fin d → ℤ) (_ : mem j w),
          ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) * u j w x)) ^ Q ≤
        ENNReal.ofReal ((lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
          ∑ vB ∈ Zanc, X vB x ^ Q := by
    intro x
    have hstep := sup_collapse_le (u := fun j w => u j w x) (X := ⨆ vB ∈ Zanc, X vB x)
      (fun j hj1 hj2 w hw => hcell x j hj1 hj2 w hw)
    refine le_trans (ENNReal.rpow_le_rpow hstep hQ.le) ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hQ.le,
      ← ENNReal.ofReal_rpow_of_nonneg hcoef0 hQ.le]
    exact mul_le_mul' le_rfl (PortableHistory.iSup_finset_rpow_le_sum Zanc (fun vB => X vB x) hQ)
  -- the stationarity comparison, totalled by the count
  calc ∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ n) (w : Fin d → ℤ) (_ : mem j w),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) * u j w x)) ^ Q ∂P
      ≤ ∫⁻ x, ENNReal.ofReal ((lam * CW *
            (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
          ∑ vB ∈ Zanc, X vB x ^ Q ∂P := lintegral_mono hpath
    _ = ENNReal.ofReal ((lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
          ∫⁻ x, ∑ vB ∈ Zanc, X vB x ^ Q ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
          ∑ vB ∈ Zanc, ∫⁻ x, X vB x ^ Q ∂P := by
        rw [lintegral_finset_sum' Zanc fun vB _ => hmeasQ vB]
    _ ≤ ENNReal.ofReal ((lam * CW * (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (b : ℝ)))) ^ Q) *
          (ENNReal.ofReal ((2 + Real.sqrt d * Khop) ^ d *
              (3 : ℝ) ^ ((n - b) * (d : ℤ))) *
            centeredHistory P Q rhoMax q jStar b) := by
        refine mul_le_mul' le_rfl ?_
        exact ancestor_total_le hd hQ.le hP hq hlb hbn hK hpdb hZanc

end

end Transport
end HighContrast
end Homogenization
