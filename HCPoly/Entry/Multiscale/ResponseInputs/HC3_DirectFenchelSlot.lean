import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsFenchelPair

/-!
# The two slots of the full-dual pairing against the source-load head

The two cutoff-mean rows of `p.response.transfer` carry the two crossed pairings `⟨N₁, Y₂⟩` and
`⟨Y₁, N₂⟩` under separate absolute values, so each slot is bounded on its own.  The direct
full-dual Fenchel pairing bounds each slot by its own annealed coarse-block norm times the square
root of the cell energy.  Adding the other, nonnegative, annealed norm on the right puts both in
the single shape the descendant row consumes, with the source-load head
`G_V = |b_V^{1/2} Y₁| + |S_{*,V}^{-1/2} Y₂|` and the scalar deficit
`D_V = ½ ⨍_V ⟨∇v, S ∇v⟩`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The gradient slot of the full-dual pairing against the source-load head.**  The pairing of
the annealed flux `Y₂` with the gradient cell average of the optimizer state is at most the
source-load head of the cell times the square root of twice the half cell energy. -/
theorem abs_vecDot_cellAverage_grad_le_head {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (2 * ((1 / 2 : ℝ) *
            volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
  have hgrad := abs_vecDot_cellAverage_grad_le hConv hEll hvol v Y.2 hA2
  have hA1_nonneg : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1) := hA1
  have hle : Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2))
      ≤ Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :=
    le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hE : 0 ≤ Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
    Real.sqrt_nonneg _
  calc
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1|
        ≤ Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := hgrad
    _ ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
        mul_le_mul_of_nonneg_right hle hE
    _ = (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (2 * ((1 / 2 : ℝ) *
              volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
        rw [show 2 * ((1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v))
            = volumeAverage V (scalarVariationEnergyIntegrand b v) by ring]

/-- **The flux slot of the full-dual pairing against the source-load head.**  The pairing of the
annealed gradient `Y₁` with the flux cell average of the optimizer state is at most the
source-load head of the cell times the square root of twice the half cell energy. -/
theorem abs_vecDot_cellAverage_flux_le_head {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :
    |vecDot Y.1 (cellAverage V (optimizerField b v)).2|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (2 * ((1 / 2 : ℝ) *
            volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
  have hflux := abs_vecDot_cellAverage_flux_le hConv hEll hvol v Y.1 hA1
  have hA2_nonneg : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2) := hA2
  have hle : Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
      ≤ Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hE : 0 ≤ Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
    Real.sqrt_nonneg _
  calc
    |vecDot Y.1 (cellAverage V (optimizerField b v)).2|
        ≤ Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := hflux
    _ ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
        mul_le_mul_of_nonneg_right hle hE
    _ = (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (2 * ((1 / 2 : ℝ) *
              volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
        rw [show 2 * ((1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v))
            = volumeAverage V (scalarVariationEnergyIntegrand b v) by ring]

end

end Homogenization.HighContrast.Multiscale
