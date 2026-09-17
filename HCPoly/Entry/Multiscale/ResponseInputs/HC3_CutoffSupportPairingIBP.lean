import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportIBP
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportAffineH1
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportSolenoidal

/-!
# The cutoff pairing on a cell, after integration by parts

On a cell `U`, the cutoff-weighted pairing of the gradient defect of an `A`-harmonic function
against its flux defect equals minus the pairing of the centred potential against the flux defect
contracted with the gradient of the cutoff.  This is the normalization by the cell volume of the
integration-by-parts identity `integral_cutoff_vecDot_grad_eq_neg_integral_vecDot_gradCutoff`
applied to the flux defect and to the affine defect of the potential; it is the step that opens
the cutoff argument of the response estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1,
(A.4)) by moving one derivative off the optimizer and onto the cutoff.

The centring constant `c` is arbitrary; it is chosen later to centre the potential.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- On a cell `U`, the volume average of the cutoff-weighted pairing of the gradient defect
`∇v - Y.1` against the flux defect `b ∇v - Y.2` of an `A`-harmonic function `v` equals the
negative of the volume average of the pairing of the centred potential `v - Y.1 · x - c` against
the flux defect contracted with the gradient of the cutoff.  Both pairings are assumed
integrable on `U`.  This is the normalized form of the integration-by-parts step in the
derivation of the cutoff estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem volumeAverage_cutoff_pairing_eq_neg {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {b : CoeffField d}
    (u : AHarmonicFunction b U)
    (hflux : MemVectorL2 U (fun x => matVecMul (b x) (u.toH1.grad x)))
    (Y : BlockVec d) (c : ℝ)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U)
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1)) U)
    (hint2 : MeasureTheory.IntegrableOn (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j))) U) :
    volumeAverage U (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -volumeAverage U (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
          vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
            (fun j => (fderiv ℝ φ x) (basisVec j))) := by
  have hsol : IsSolenoidalOn U (fun x => matVecMul (b x) (u.toH1.grad x) - Y.2) :=
    isSolenoidalOn_fluxDefect_of_finiteMeasure u hflux Y.2
  have hkey :
      (∫ x in U, φ x * vecDot (u.toH1.grad x - Y.1)
          (matVecMul (b x) (u.toH1.grad x) - Y.2))
        = -∫ x in U, (u.toH1.toFun x - vecDot Y.1 x - c) *
            vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
              (fun j => (fderiv ℝ φ x) (basisVec j)) := by
    have hswap :
        (∫ x in U, φ x * vecDot (u.toH1.grad x - Y.1)
            (matVecMul (b x) (u.toH1.grad x) - Y.2))
          = ∫ x in U, φ x * vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
              (u.toH1.grad x - Y.1) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [vecDot_comm]
    rw [hswap]
    have hibp := integral_cutoff_vecDot_grad_eq_neg_integral_vecDot_gradCutoff (U := U) hU
      (g := fun x => matVecMul (b x) (u.toH1.grad x) - Y.2) hsol
      (affineDefectH1 hU u.toH1 Y.1 c) hφ hφ_compact hφ_sub
      (by simpa only [affineDefectH1_grad] using hint1)
      (by simpa only [affineDefectH1_toFun] using hint2)
    simpa only [affineDefectH1_grad, affineDefectH1_toFun] using hibp
  change volumeAverage U (fun x => φ x * vecDot (u.toH1.grad x - Y.1)
      (matVecMul (b x) (u.toH1.grad x) - Y.2))
    = -volumeAverage U (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
        vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
          (fun j => (fderiv ℝ φ x) (basisVec j)))
  simp only [volumeAverage]
  rw [hkey, mul_neg]

end

end Homogenization.HighContrast.Multiscale
