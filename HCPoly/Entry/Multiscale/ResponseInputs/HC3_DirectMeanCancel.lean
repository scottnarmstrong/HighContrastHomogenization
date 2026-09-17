import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffEnergyDefect
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportProj

/-!
# Cancellation of constant cell means after expectation

In the centred cutoff decomposition of `p.response.transfer`, the constant cell means cancel after
expectation.  The scale-`s` translations of the grid are integral, so the cell averages of the
cutoff fluctuation share a common annealed value.  Exact partition averaging turns their average
over the generation-`(t - n)` triadic subdivision of the terminal cell into the average of `φ - 1`
over that cell, and that average vanishes because the cutoff class has volume average one.  The
same partition then shows that any weighting of a family of cell functionals with a common
annealed value and mean-zero normalized weights integrates to zero.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Cancellation of the cell means of the cutoff fluctuation.**  The normalized sum of the cell
averages of `φ - 1` over the `3 ^ (n * d)` depth-`n` triadic subcells of the adapted cell
`HighContrast.adaptedCell qq t` equals the average of `φ - 1` over that cell, which is zero because
`φ` has volume average one there.  This is the first cancellation in `p.response.transfer`. -/
theorem avsum_volumeAverage_sub_one_eq_zero {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq)
    (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    (hint : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell qq t))
    (hvol : (volume (HighContrast.adaptedCell qq t)).toReal ≠ 0)
    (hφint : IntegrableOn φ (HighContrast.adaptedCell qq t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1)
      = 0 := by
  rw [avsum_volumeAverage_eq qq hq t n hint]
  exact volumeAverage_sub_one_eq_zero (HighContrast.adaptedCell qq t)
    (IsResponseCutoff.volumeAverage_eq_one hφ) hvol hφint

/-- **Mean-zero weighting of a common annealed value.**  If each cell functional `G w` has the same
annealed value `m` and the weights `c w` have normalized sum zero, then the annealed integral of
the weighted sum vanishes.  The common value is the one supplied by the integrality of the
scale-`s` translations; this is the second cancellation in `p.response.transfer`. -/
theorem integral_avsum_mul_eq_zero {d : ℕ} {α : Type*} [MeasurableSpace α] (P : Measure α)
    (n : ℕ) (c : (Fin d → ℤ) → ℝ) (G : (Fin d → ℤ) → α → ℝ) (m : ℝ)
    (hc : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hG : ∀ w ∈ triadicIndexBox d n, (∫ a, G w a ∂P) = m)
    (hint : ∀ w ∈ triadicIndexBox d n, Integrable (G w) P) :
    (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P) = 0 := by
  calc (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P)
      = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∫ a, ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P := by
        rw [integral_const_mul]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ∫ a, c w * G w a ∂P := by
        rw [integral_finsetSum (triadicIndexBox d n)
          (fun w hw => (hint w hw).const_mul (c w))]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * m := by
        have hsum : (∑ w ∈ triadicIndexBox d n, ∫ a, c w * G w a ∂P)
            = ∑ w ∈ triadicIndexBox d n, c w * m :=
          Finset.sum_congr rfl (fun w hw => by rw [integral_const_mul, hG w hw])
        rw [hsum]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ((∑ w ∈ triadicIndexBox d n, c w) * m) := by
        rw [← Finset.sum_mul]
    _ = ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w) * m := by
        rw [← mul_assoc]
    _ = 0 := by
        rw [hc, zero_mul]

end

end Homogenization.HighContrast.Multiscale
