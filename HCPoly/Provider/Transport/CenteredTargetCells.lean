/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationHigh
import HCPoly.Provider.Transport.KernelExponents

/-!
# The target cells of the transported centered history

The centered history of the new grid at the new terminal scale runs a maximum
over every aligned cell of every scale of the range inside the terminal cell,
and the transport converts that maximum into a sum over the target scales of
per-cell contributions.  Two steps do it, and both are the printed ones.

*Over the scales.*  The range of scales is finite, so the `Q`-th power of the
maximum over it is at most the sum of the `Q`-th powers of the maxima at the
single scales.  This is the same max-to-sum the fixed-grid majorization uses,
run over the whole range rather than over the two halves of a checkpoint split.

*Over the cells of one scale.*  There are exactly `3^{d(n-j)}` aligned scale-`j`
cells in the scale-`n` terminal cell, and they are integer translates of one
another, so by stationarity of the coefficient law they all contribute the same
lower integral; max-to-sum leaves only their number.  Against the maximal weight
`3^{-ρ_max(n-j)}`, raised to the power `Q`, that number is exactly the printed
target coefficient `3^{-(Qρ_max-d)(n-j)}`, the cost of replacing the maximum over
target cells by a sum.

The result is stated at the *terminal* normalization `E_n^{q'}` throughout: the
transport never renormalizes a target cell to its own scale, because the
estimate it feeds the target with — the filling of the cell by the old grid —
is itself written at the terminal normalization.  That is what makes the
per-cell quantity on the right the one the source rows bound, and not the
centered moment of the new grid, which is the quantity the proposition is
proving small.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix ENNReal

noncomputable section

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar : ℤ}

/-! ## The cells of one target scale -/

/-- **The cost of replacing the maximum over target cells by a sum**, at the
level of the `Q`-th power.  The centered maximum over the aligned scale-`j`
cells of the scale-`n` terminal cell, measured at the terminal normalization and
weighted by
`3^{-ρ_max(n-j)}`, has `Q`-th moment at most the printed target coefficient
`3^{-(Qρ_max-d)(n-j)}` times the `Q`-th moment of the single cell at the origin.

Only two facts are used: the aligned cells of a scale are integer translates of
the cell at the origin, so stationarity of the coefficient law gives them all the
same moment; and there are exactly `3^{d(n-j)}` of them. -/
theorem centered_scale_count_le [NeZero d] [IsProbabilityMeasure P] {Q rhoMax : ℝ}
    (hQ : 0 < Q) (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q)
    (hlj : l ≤ jStar) {j n : ℤ} (hj : jStar ≤ j) (hjn : j ≤ n)
    (hpdn : Book.Ch02.BlockPosDef (adaptedMean P q n)) :
    ∫⁻ x, (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q n),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q n))) ^ Q ∂P ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(Q * rhoMax - (d : ℝ)) * ((n : ℝ) - (j : ℝ)))) *
        ∫⁻ x, ENNReal.ofReal (blockSize
            (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
            (adaptedMean P q n)) ^ Q ∂P := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hlj' : l ≤ j := le_trans hlj hj
  obtain ⟨Z, hZ, hcard, -, -, -, hint⟩ := Recurrence.aligned_subdivision hq hlj' hjn
  have hmem : ∀ w : Fin d → ℤ, adaptedCellCenter q j w ∈ adaptedCell q n → w ∈ Z := by
    intro w hw
    have hw' : w ∈ (↑Z : Set (Fin d → ℤ)) := by rw [hZ]; exact hw
    exact hw'
  -- the statistic at the cell of the origin
  have hcell : AEMeasurable (fun x : CoeffSpace d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
        blockSize (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
          (adaptedMean P q n)) ^ Q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((PortableHistory.aemeasurable_blockSize_coarseBlock_sub
          (Recurrence.hasMeasurableCoarseBlock_adaptedCell P hqPD j)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q n) hpdn).const_mul _))
  -- every aligned cell contributes the moment of the cell at the origin
  have hterm : ∀ w ∈ Z,
      ∫⁻ x, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q n)) ^ Q ∂P =
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ)))) ^ Q *
        ∫⁻ x, ENNReal.ofReal (blockSize
            (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
            (adaptedMean P q n)) ^ Q ∂P := by
    intro w hw
    obtain ⟨vw, hvw⟩ := hint w hw
    have hshift : (fun x : CoeffSpace d =>
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q n)) ^ Q) =
        fun x : CoeffSpace d =>
          (fun z : CoeffSpace d => ENNReal.ofReal
            ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
              blockSize (blockSub (coarseBlock (adaptedCell q j) z) (adaptedMean P q j))
                (adaptedMean P q n)) ^ Q) (translateCoeff vw x) := by
      funext x
      rw [Recurrence.adaptedResponse_eq_coarseBlock_translateCoeff hvw x]
    rw [hshift, PortableHistory.lintegral_comp_translateCoeff hP hcell vw,
      ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hQ.le ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg h3.le _),
      ENNReal.mul_rpow_of_nonneg _ _ hQ.le]
  -- the counting factor is the printed target coefficient
  have hconst : (Z.card : ℝ≥0∞) *
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ)))) ^ Q =
      ENNReal.ofReal ((3 : ℝ) ^ (-(Q * rhoMax - (d : ℝ)) * ((n : ℝ) - (j : ℝ)))) := by
    have htoNat : (((n - j).toNat : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := by
      have hz : ((n - j).toNat : ℤ) = n - j := Int.toNat_of_nonneg (by omega)
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
    have hcast : ((Z.card : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) - (j : ℝ))) := by
      rw [hcard]
      push_cast
      rw [← Real.rpow_natCast (3 : ℝ) (d * (n - j).toNat)]
      congr 1
      push_cast [htoNat]
      ring
    rw [← ENNReal.ofReal_natCast, hcast,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg h3.le _) hQ.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg h3.le _),
      ← Real.rpow_mul h3.le, ← Real.rpow_add h3]
    congr 1
    ring_nf
  calc ∫⁻ x, (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q n),
          ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
              (adaptedMean P q n))) ^ Q ∂P
      ≤ ∫⁻ x, ∑ w ∈ Z, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
              (adaptedMean P q n)) ^ Q ∂P := by
        refine lintegral_mono fun x => le_trans (ENNReal.rpow_le_rpow ?_ hQ.le)
          (PortableHistory.iSup_finset_rpow_le_sum Z _ hQ)
        exact iSup_le fun w => iSup_le fun hw => le_iSup_of_le w
          (le_iSup_of_le (hmem w hw) le_rfl)
    _ = ∑ w ∈ Z, ∫⁻ x, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
              (adaptedMean P q n)) ^ Q ∂P := by
        refine lintegral_finset_sum' Z fun w _ => ?_
        exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          (ENNReal.measurable_ofReal.comp_aemeasurable
            ((PortableHistory.aemeasurable_blockSize_coarseBlock_sub
              (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hqPD j w)
              (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
              (Recurrence.isSymmetricBlockMat_adaptedMean P q n) hpdn).const_mul _))
    _ = ∑ _w ∈ Z, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ)))) ^ Q *
          ∫⁻ x, ENNReal.ofReal (blockSize
            (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
            (adaptedMean P q n)) ^ Q ∂P := Finset.sum_congr rfl hterm
    _ = (Z.card : ℝ≥0∞) * ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ)))) ^ Q *
          ∫⁻ x, ENNReal.ofReal (blockSize
            (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
            (adaptedMean P q n)) ^ Q ∂P := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ = _ := by rw [hconst]

/-! ## The scales of the range -/

/-- **The centered history splits over the target scales.**  The range of scales
of `e.scale.selection.fluctuation.history` is finite, so the `Q`-th power of the
maximum over it is at most the sum, over the scales, of the `Q`-th powers of the
maxima at the single scales. -/
theorem centeredHistory_le_sum_scales [NeZero d] [IsProbabilityMeasure P] {Q rhoMax : ℝ}
    (hQ : 0 < Q) (hq : IsRoundedGrid l q) {n : ℤ}
    (hpdn : Book.Ch02.BlockPosDef (adaptedMean P q n)) :
    centeredHistory P Q rhoMax q jStar n ≤
      ∑ j ∈ Finset.Icc jStar n,
        ∫⁻ x, (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q n),
          ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
              (adaptedMean P q n))) ^ Q ∂P := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  rw [centeredHistory]
  calc ∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ n) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q n),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q n))) ^ Q ∂P
      ≤ ∫⁻ x, ∑ j ∈ Finset.Icc jStar n,
          (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q n),
            ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ))) *
              blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
                (adaptedMean P q n))) ^ Q ∂P := by
        refine lintegral_mono fun x => le_trans (ENNReal.rpow_le_rpow ?_ hQ.le)
          (PortableHistory.iSup_finset_rpow_le_sum (Finset.Icc jStar n) _ hQ)
        exact iSup_le fun j => iSup_le fun h1 => iSup_le fun h2 =>
          le_iSup_of_le j (le_iSup_of_le (Finset.mem_Icc.mpr ⟨h1, h2⟩) le_rfl)
    _ = _ := by
        refine lintegral_finset_sum' _ fun j _ => ?_
        exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          (PortableHistory.aemeasurable_adaptedCellSup hqPD
            (Recurrence.isSymmetricBlockMat_adaptedMean P q n) hpdn
            ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (j : ℝ)))) j (adaptedCell q n))

/-! ## The two steps together -/

/-- **The centered history against the per-cell moments of the target scales.**
Combining the split over the scales with the target multiplicity: the centered
history of the grid at the terminal scale is at most the sum over the scales of
the range of the printed target coefficient times the `Q`-th moment of the
centered response of a single cell of that scale, measured at the terminal
normalization.

This is the form the transport reads: the right side no longer mentions the
grid's own centered moments, only the per-cell statistic that the filling of
each target cell by the old grid bounds. -/
theorem centeredHistory_le_sum_cell_moments [NeZero d] [IsProbabilityMeasure P]
    {Q rhoMax : ℝ} (hQ : 0 < Q) (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hq : IsRoundedGrid l q) (hlj : l ≤ jStar) {n : ℤ}
    (hpdn : Book.Ch02.BlockPosDef (adaptedMean P q n)) :
    centeredHistory P Q rhoMax q jStar n ≤
      ∑ j ∈ Finset.Icc jStar n,
        ENNReal.ofReal ((3 : ℝ) ^ (-(Q * rhoMax - (d : ℝ)) * ((n : ℝ) - (j : ℝ)))) *
          ∫⁻ x, ENNReal.ofReal (blockSize
              (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
              (adaptedMean P q n)) ^ Q ∂P := by
  refine le_trans (centeredHistory_le_sum_scales hQ hq hpdn) (Finset.sum_le_sum fun j hj => ?_)
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  exact centered_scale_count_le hQ hP hq hlj hj1 hj2 hpdn

end Window

end

end Transport
end HighContrast
end Homogenization
