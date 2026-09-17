import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPairingIBP
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportChangeVar

/-!
# The cutoff pairing after integration by parts, written on the reference cube

On the adapted cell `HighContrast.adaptedCell q t`, the integration-by-parts form of the
cutoff pairing is the negative of the volume average of the centred potential against the
flux defect contracted with the gradient of the cutoff.  Composing that identity with the
change of variables `x = q y` that identifies the normalized average on the adapted cell
with the normalized average on the reference cube `originCube d t` gives the form of the
cutoff argument in which the negative-Besov duality of the response estimate
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)) applies.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The integration-by-parts identity for the cutoff pairing on the adapted cell
`HighContrast.adaptedCell q t`, transported to the reference cube.  The volume average on the
adapted cell of the cutoff-weighted pairing of the gradient defect `∇v - Y.1` against the
flux defect `b ∇v - Y.2` equals the negative of the cube average on `originCube d t` of the
centred potential `v (q y) - Y.1 · (q y) - c` against the flux defect evaluated at `q y`,
contracted with the gradient of the cutoff at `q y`.  Both pairings are assumed integrable
on the adapted cell.  This is the form of the cutoff estimate `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) in which the negative-Besov duality is applied. -/
theorem cubeAverage_cutoff_pairing_eq_neg {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    (hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t))
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t))]
    {b : CoeffField d} (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hflux : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (b x) (u.toH1.grad x)))
    (Y : BlockVec d) (c : ℝ)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ HighContrast.adaptedCell q t)
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (HighContrast.adaptedCell q t))
    (hint2 : MeasureTheory.IntegrableOn (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j))) (HighContrast.adaptedCell q t)) :
    volumeAverage (HighContrast.adaptedCell q t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -cubeAverage (originCube d t) (fun y =>
          (u.toH1.toFun (matVecMul q y) - vecDot Y.1 (matVecMul q y) - c) *
            vecDot (matVecMul (b (matVecMul q y)) (u.toH1.grad (matVecMul q y)) - Y.2)
              (fun j => (fderiv ℝ φ (matVecMul q y)) (basisVec j))) := by
  have h := volumeAverage_cutoff_pairing_eq_neg (U := HighContrast.adaptedCell q t) hU u hflux Y c
    hφ hφ_compact hφ_sub hint1 hint2
  have hcv := volumeAverage_adaptedCell_eq_cubeAverage_comp (q := q) hq t
    (fun x => (u.toH1.toFun x - vecDot Y.1 x - c) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j)))
  calc volumeAverage (HighContrast.adaptedCell q t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -volumeAverage (HighContrast.adaptedCell q t) (fun x =>
          (u.toH1.toFun x - vecDot Y.1 x - c) *
            vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
              (fun j => (fderiv ℝ φ x) (basisVec j))) := h
    _ = -cubeAverage (originCube d t) (fun y =>
          (u.toH1.toFun (matVecMul q y) - vecDot Y.1 (matVecMul q y) - c) *
            vecDot (matVecMul (b (matVecMul q y)) (u.toH1.grad (matVecMul q y)) - Y.2)
              (fun j => (fderiv ℝ φ (matVecMul q y)) (basisVec j))) := by
        rw [hcv]

end

end Homogenization.HighContrast.Multiscale
