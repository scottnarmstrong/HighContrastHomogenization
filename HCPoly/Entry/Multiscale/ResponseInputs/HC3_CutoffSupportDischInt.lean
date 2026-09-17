import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportFluxCube
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportSolenoidal
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportZeroAvg
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportChangeVar
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportAdjoint
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPairingInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportState
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportProj
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportAffineH1
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportXiDischarge
import HCPoly.Entry.Multiscale.ResponseInputs.H1LinearPullback

/-!
# The integrability hypotheses of the pathwise cutoff estimate

The pathwise cutoff pairing bound of `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4)) is
assembled in `abs_volumeAverage_cutoff_pairing_le_of_inputs` with several analytic inputs exposed as
hypotheses: the integrability of the cutoff-weighted pairing and of the centred-potential pairing on
the adapted cell, the integrability on the reference cube of the pulled-back flux defect against the
pulled-back cutoff gradient and of that pairing multiplied by the centred potential, and the
vanishing of the cube average of the flux defect against the cutoff gradient.

The hypotheses only assert what the caller already has: `IsResponseCutoff (respGrid jStar F) t φ`,
positive definiteness of the canonical metric with the grid-depth inequality `2 * d ≤ 3 ^ jStar`, and
an almost-everywhere uniformly elliptic representative of the coefficient on the cell.  This file
discharges each hypothesis from that data.  The fields occurring in the pairings are square
integrable on the cell (`e.response.cutoff.estimate`): the optimizer flux by ellipticity, its
gradient because the optimizer is `H¹`, the pulled-back flux on the cube by the change of variables,
and the cutoff and its gradient are bounded there.

Paper: `e.response.cutoff.estimate` and the negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)).
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- **The cut-off-weighted pairing is integrable on the adapted cell.**  If the coefficient `b`
agrees almost everywhere on `respCell jStar F t` with a field uniformly elliptic there and `u` is
`b`-harmonic on the cell, then the cutoff `φ` of the response class times the Euclidean pairing of
the flux defect `b ∇u − Y.2` with the centred gradient `∇u − Y.1` is integrable on the cell.  This is
the `hint1` input of the pathwise cutoff estimate `e.response.cutoff.estimate`: the flux defect and
the gradient defect are both coordinatewise square integrable on the cell, and the cutoff is bounded
and measurable. -/
theorem hint1_of_inputs {d : ℕ} [NeZero d] {jStar : ℕ} {F : BlockMat d} {t : ℤ}
    {φ : Vec d → ℝ} {b : CoeffField d}
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d) :
    MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (respCell jStar F t) := by
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hbf⟩ := hb
  have hcoords :=
    memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u Y
  have hfin : IsFiniteMeasure (volume.restrict (respCell jStar F t)) := by
    simpa only [respCell] using
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  refine integrableOn_cutoff_pairing_of_coords (V := respCell jStar F t)
    (A := fun x => matVecMul (b x) (u.toH1.grad x) - Y.2)
    (B := fun x => u.toH1.grad x - Y.1) ?_ ?_ ?_ ?_
  · intro i
    simpa only [optimizerField, Prod.snd_sub, respCell] using hcoords.2 i
  · intro i
    simpa only [optimizerField, Prod.fst_sub, respCell] using hcoords.1 i
  · refine ⟨2, fun x => ?_⟩
    rw [abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  · exact hφ.contDiff.continuous.aestronglyMeasurable

end

end Homogenization.HighContrast.Multiscale
