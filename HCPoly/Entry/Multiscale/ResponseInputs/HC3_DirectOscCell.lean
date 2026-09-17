import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectFenchelSlot
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRestrictResp

/-!
# The crossed pairing of the terminal optimizer on a descendant cell

Each generation increment of the descendant sum of `p.response.transfer` pairs the annealed mean
`Y` with the cell average, over a descendant cell `V` of the terminal cell `U`, of the state of
the terminal optimizer `u`.  Restricting `u` to `V` changes neither its gradient nor its flux, so
the Fenchel probe applies on `V` with the pathwise coarse block of `V`, and both crossed slots
are controlled by the source-load head of `V` times the square root of twice the half cell energy
of `u` on `V`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The state of the restricted optimizer is the state of the optimizer.**  Restricting an
`a`-harmonic function from `U` to an open subset `V` on which the coefficient is elliptic does not
change the doubled optimizer state. -/
theorem optimizerField_restrictOfIsEllipticFieldOn {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (u : AHarmonicFunction a U) :
    optimizerField a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) = optimizerField a u := by
  funext x
  have hgrad : (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simp only [optimizerField, hgrad]

/-- **The crossed pairing of the terminal optimizer on a descendant cell.**  Both crossed slots
of the pairing of the annealed mean `Y` with the cell average of the terminal optimizer state on
a descendant cell are at most the source-load head of that cell times the square root of twice
the half cell energy.  This is the pathwise input of the descendant sum of
`p.response.transfer`. -/
theorem abs_volumeAverage_cross_le_head_mul_sqrt {d : ℕ} [NeZero d] {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    (hConv : IsOpenBoundedConvexDomain V)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (hvol : 0 < (volume V).toReal) (u : AHarmonicFunction a U) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2))
    (hX1 : ∀ i, IntegrableOn (fun x => (optimizerField a u x).1 i) V)
    (hX2 : ∀ i, IntegrableOn (fun x => (optimizerField a u x).2 i) V) :
    |volumeAverage V (fun x => vecDot Y.2 (optimizerField a u x).1)|
          ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2)))
            * Real.sqrt (2 * ((1 / 2 : ℝ) *
                volumeAverage V (scalarVariationEnergyIntegrand a u)))
      ∧ |volumeAverage V (fun x => vecDot Y.1 (optimizerField a u x).2)|
          ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2)))
            * Real.sqrt (2 * ((1 / 2 : ℝ) *
                volumeAverage V (scalarVariationEnergyIntegrand a u))) := by
  have hg : volumeAverage V (fun x => vecDot Y.2 (optimizerField a u x).1)
      = vecDot Y.2 (cellAverage V (optimizerField a u)).1 := by
    rw [volumeAverage_vecDot_left Y.2 (fun x => (optimizerField a u x).1) hX1]
    rfl
  have hf : volumeAverage V (fun x => vecDot Y.1 (optimizerField a u x).2)
      = vecDot Y.1 (cellAverage V (optimizerField a u)).2 := by
    rw [volumeAverage_vecDot_left Y.1 (fun x => (optimizerField a u x).2) hX2]
    rfl
  have hgrad := abs_vecDot_cellAverage_grad_le_head hConv hEll hvol
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) Y hA1 hA2
  have hflux := abs_vecDot_cellAverage_flux_le_head hConv hEll hvol
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) Y hA1 hA2
  rw [scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll u] at hgrad hflux
  rw [optimizerField_restrictOfIsEllipticFieldOn hU hV hVU hEll u] at hgrad hflux
  rw [hg, hf]
  exact ⟨hgrad, hflux⟩

end

end Homogenization.HighContrast.Multiscale
