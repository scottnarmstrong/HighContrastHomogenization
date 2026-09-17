import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsSubcellDiffDual
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cmp

/-!
# The subcell dual pairing at an almost-everywhere elliptic coefficient

The cell half of the cutoff-mean row of `p.response.transfer` pairs, on each coarse subcell of the
terminal cell, the dual variable `Y` against the difference between the cell mean of the terminal
optimizer's doubled state and the cell mean of that subcell's own optimizer.  The direct full-dual
pairing of AK.HC (A.4) bounds it by the subcell's two-term head times the square root of twice the
subcell deficit.  That estimate is stated for a pointwise elliptic coefficient; the response
coefficients `respCoeff∓ F a` are elliptic only almost everywhere, so this module runs it at a
pointwise elliptic representative and transports every quantity back across the a.e. replacement,
which leaves each of them invariant.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cell average of the doubled optimizer field is unchanged when the coefficient field is
replaced by an a.e.-equal one carrying a solution with the same gradient.  The two gradient slots
coincide on the nose, and the two flux slots agree wherever the coefficients agree, so both volume
averages coincide. -/
private theorem cellAverage_optimizerField_congr_of_ae_eq {d : ℕ} {U U' V : Set (Vec d)}
    {b c : CoeffField d} (u : AHarmonicFunction b U) (v : AHarmonicFunction c U')
    (hgrad : v.toH1.grad = u.toH1.grad) (hae : b =ᵐ[volumeMeasureOn V] c) :
    cellAverage V (optimizerField b u) = cellAverage V (optimizerField c v) := by
  refine Prod.ext ?_ ?_ <;> funext i
  · simp only [cellAverage, optimizerField, hgrad]
  · simp only [cellAverage, optimizerField, hgrad, volumeAverage]
    exact congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z)
      (integral_congr_ae (hae.mono fun x hx => by simp [hx]))

/-- The cell half of the cutoff-mean row of `p.response.transfer`.  Let `f` be pointwise elliptic
on the terminal cell `HighContrast.adaptedCell q t` and let `b` agree with `f` almost everywhere
there.  For a `b`-harmonic `u` on the terminal cell, a subcell maximizer `v` on the aligned subcell
`adaptedCellAtCenter q (t - n) w`, and a state `Y = (P, Q)`, the pairing of `Y` with the difference of
the two cell averages is bounded by the sum of the square roots of the two diagonal coarse-block
forms of `Y`, times the square root of twice the subcell response deficit of `u`.  The bound holds
for `b` itself although only the representative `f` is pointwise elliptic, because every quantity
in the estimate is invariant under the a.e. replacement. -/
theorem abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n)
    (v : AHarmonicFunction b (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hmaxV : IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b v)
    (Y : BlockVec d) :
    |vecDot Y.2 ((cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)).1
          - (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)).1)
        + vecDot Y.1 ((cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)).2
          - (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b).lowerRight Y.2)))
        * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
            - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))) := by
  have hU : IsOpen (HighContrast.adaptedCell q t) := isOpen_adaptedCell_of_isUnit hq t
  have hV : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos q hq (t - (n : ℤ)) w
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    isEllipticFieldOn_subset hEll hVU hV.measurableSet
  have haeV : b =ᵐ[volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  have hmaxV' : IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
      (aHarmonicFunctionOfAEEqCoeff haeV v) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff haeV p r hmaxV
  have huV_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      ((aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV) :=
    hdata.weakFlux
      ((aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV)
  have hv_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      (aHarmonicFunctionOfAEEqCoeff haeV v) :=
    hdata.weakFlux (aHarmonicFunctionOfAEEqCoeff haeV v)
  have hmain := abs_dualPairing_diff_cellAverage_le (U := HighContrast.adaptedCell q t)
    (V := adaptedCellAtCenter q (t - (n : ℤ)) w)
    (u := aHarmonicFunctionOfAEEqCoeff hae u) (v := aHarmonicFunctionOfAEEqCoeff haeV v)
    hVU hU hV hConv hEllV hvol
    hmaxV' huV_int hv_int
    (hdata.response p r (aHarmonicFunctionOfAEEqCoeff haeV v))
    (hdata.firstVariation p r (aHarmonicFunctionOfAEEqCoeff haeV v)
      (AHarmonicFunction.addSMulOfIntegrable
        ((aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV)
        (aHarmonicFunctionOfAEEqCoeff haeV v) huV_int hv_int (-1)))
    (hdata.energy (AHarmonicFunction.addSMulOfIntegrable
      ((aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV)
      (aHarmonicFunctionOfAEEqCoeff haeV v) huV_int hv_int (-1))) Y
  have hA_u : cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField f
        ((aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV))
      = cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u) :=
    cellAverage_optimizerField_congr_of_ae_eq
      ((aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV) u
      (grad_aHarmonicFunctionOfAEEqCoeff hae u).symm haeV.symm
  have hA_v : cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (optimizerField f (aHarmonicFunctionOfAEEqCoeff haeV v))
      = cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) :=
    cellAverage_optimizerField_congr_of_ae_eq
      (aHarmonicFunctionOfAEEqCoeff haeV v) v
      (grad_aHarmonicFunctionOfAEEqCoeff haeV v).symm haeV.symm
  have hC : coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      = coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b :=
    (coarseBlockMatrix_congr_of_ae_eq haeV).symm
  have hD : ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
      = ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b :=
    (responseJ_congr_of_ae_eq_subset hVU hae p r).symm
  have hE : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) f p r
          ((aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV))
      = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) := by
    simpa only [scalarResponseIntegrand, AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn,
      H1Function.restrict] using!
      (volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae p r u)
  simpa only [hA_u, hA_v, hC, hD, hE] using hmain

end

end Homogenization.HighContrast.Multiscale
