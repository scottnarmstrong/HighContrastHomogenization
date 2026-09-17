import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsFenchelPair
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsBlockPSD
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakQuadraticResponse

/-!
# The full-dual pairing of the subcell difference field

The direct full-dual pairing AK.HC, display (A.4), applied to the field that the cutoff-mean rows
produce: the difference between the terminal optimizer restricted to a scale-`s` cell and that
cell's own optimizer.  The state `Y = (P, Q)` is paired with the two slots of the cell-average
difference.  The right-hand side is the cell's own coarse-block energy of `Y` — read through the
two diagonal blocks from which the source load is built — times the square root of the scalar cell
deficit.  Because the difference energy of the two states is twice the response deficit, no
subcell optimizer survives in the statement, so no measurable selection is needed downstream.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cell average of the difference between the terminal optimizer field restricted to the
cell `V` and the cell's own optimizer obeys the direct full-dual pairing bound: paired against a
state `Y = (P, Q)`, it is controlled by the total of the square roots of the two diagonal
coarse-block forms of `Y` times the square root of twice the scalar response deficit of the
restricted terminal field. -/
theorem abs_dualPairing_diff_cellAverage_le {d : ℕ} [NeZero d] {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hU : IsOpen U) (hV : IsOpen V) (hConv : IsOpenBoundedConvexDomain V)
    [IsFiniteMeasure (volumeMeasureOn V)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam V a)
    (hvol : 0 < (volume V).toReal)
    {p q : Vec d} {u : AHarmonicFunction a U} {v : AHarmonicFunction a V}
    (hmaxV : IsResponseMaximizer V p q a v)
    (huV_int : weakFluxIntegrable V a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : IntegrableOn (scalarResponseIntegrand V a p q v) V)
    (hlin : IntegrableOn (scalarFirstVariationIntegrand V a p q v
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy : IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (Y : BlockVec d) :
    |vecDot Y.2 ((cellAverage V
            (optimizerField a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))).1
          - (cellAverage V (optimizerField a v)).1)
        + vecDot Y.1 ((cellAverage V
            (optimizerField a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))).2
          - (cellAverage V (optimizerField a v)).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2)))
        * Real.sqrt (2 * (ResponseJ V p q a
            - volumeAverage V (scalarResponseIntegrand V a p q
                (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)))) := by
  let uV : AHarmonicFunction a V := u.restrictOfIsEllipticFieldOn hU hV hVU hEll
  let w : AHarmonicFunction a V :=
    AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)
  have hwgrad : ∀ x, w.toH1.grad x = uV.toH1.grad x - v.toH1.grad x := by
    intro x
    change (AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)).toH1.grad x =
      uV.toH1.grad x - v.toH1.grad x
    rw [AHarmonicFunction.grad_addSMulOfIntegrable]
    simp [sub_eq_add_neg]
  have hcell : cellAverage V (optimizerField a w) =
      cellAverage V (optimizerField a uV) - cellAverage V (optimizerField a v) := by
    refine Prod.ext ?_ ?_
    · funext i
      change volumeAverage V (fun x => w.toH1.grad x i) =
        volumeAverage V (fun x => uV.toH1.grad x i)
          - volumeAverage V (fun x => v.toH1.grad x i)
      have hf : IntegrableOn (fun x => uV.toH1.grad x i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2 uV.toH1.grad_memVectorL2 i
      have hg : IntegrableOn (fun x => v.toH1.grad x i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2 v.toH1.grad_memVectorL2 i
      have hsub : volumeAverage V (fun x => uV.toH1.grad x i - v.toH1.grad x i) =
          volumeAverage V (fun x => uV.toH1.grad x i)
            - volumeAverage V (fun x => v.toH1.grad x i) :=
        volumeAverage_sub hf hg
      calc volumeAverage V (fun x => w.toH1.grad x i)
          = volumeAverage V (fun x => uV.toH1.grad x i - v.toH1.grad x i) := by
            apply congrArg (volumeAverage V)
            funext x
            simp [hwgrad x]
        _ = volumeAverage V (fun x => uV.toH1.grad x i)
              - volumeAverage V (fun x => v.toH1.grad x i) := hsub
    · funext i
      change volumeAverage V (fun x => matVecMul (a x) (w.toH1.grad x) i) =
        volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i)
          - volumeAverage V (fun x => matVecMul (a x) (v.toH1.grad x) i)
      have hf : IntegrableOn (fun x => matVecMul (a x) (uV.toH1.grad x) i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll uV.toH1.grad_memVectorL2) i
      have hg : IntegrableOn (fun x => matVecMul (a x) (v.toH1.grad x) i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.toH1.grad_memVectorL2) i
      have hsub : volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i
            - matVecMul (a x) (v.toH1.grad x) i) =
          volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i)
            - volumeAverage V (fun x => matVecMul (a x) (v.toH1.grad x) i) :=
        volumeAverage_sub hf hg
      calc volumeAverage V (fun x => matVecMul (a x) (w.toH1.grad x) i)
          = volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i
              - matVecMul (a x) (v.toH1.grad x) i) := by
            apply congrArg (volumeAverage V)
            funext x
            simp [hwgrad x, matVecMul_sub_vec]
        _ = volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i)
              - volumeAverage V (fun x => matVecMul (a x) (v.toH1.grad x) i) := hsub
  have henergyeq : volumeAverage V (scalarVariationEnergyIntegrand a w) =
      2 * (ResponseJ V p q a - volumeAverage V (scalarResponseIntegrand V a p q uV)) := by
    have h := h6a_difference_energy_eq_response_deficit hVU hU hV hEll hmaxV huV_int hv_int
      hresp_v hlin henergy
    have hfun : scalarVariationEnergyIntegrand a w =
        fun x => vecDot (uV.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (uV.toH1.grad x - v.toH1.grad x)) := by
      funext x
      simp only [scalarVariationEnergyIntegrand, hwgrad]
    rw [hfun]
    exact h
  have hmain := abs_dualPairing_cellAverage_le (b := a) hConv hEll hvol w Y
    (zero_le_vecDot_coarseBlockMatrix_upperLeft hConv hEll hvol Y.1)
    (zero_le_vecDot_coarseBlockMatrix_lowerRight hConv hEll hvol Y.2)
  rw [hcell, henergyeq] at hmain
  exact hmain

end

end Homogenization.HighContrast.Multiscale
