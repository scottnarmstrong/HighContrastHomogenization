import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportState

/-!
# Integrability of the cutoff-weighted pairing on a cell

The integration-by-parts form of the cutoff pairing `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) integrates the product of a bounded cutoff with the Euclidean pairing of
two square-integrable vector fields against the cell measure.  This file supplies the
integrability side conditions for that pairing, and the integrability of the squared Euclidean
length of a square-integrable vector field.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A bounded measurable weight times the Euclidean pairing of two coordinatewise square
integrable vector fields is integrable on a cell.  This is the integrability side condition of
the cutoff-weighted pairing `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem integrableOn_cutoff_pairing_of_coords {d : ℕ} {V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict V)]
    {A B : Vec d → Vec d}
    (hA : ∀ i, MeasureTheory.MemLp (fun x => A x i) 2 (MeasureTheory.volume.restrict V))
    (hB : ∀ i, MeasureTheory.MemLp (fun x => B x i) 2 (MeasureTheory.volume.restrict V))
    {φ : Vec d → ℝ} (hφb : ∃ M : ℝ, ∀ x, |φ x| ≤ M)
    (hφm : MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.volume.restrict V)) :
    MeasureTheory.IntegrableOn (fun x => φ x * vecDot (A x) (B x)) V := by
  rw [MeasureTheory.IntegrableOn]
  have hpair : Integrable (fun x => vecDot (A x) (B x)) (volume.restrict V) := by
    have hsum : Integrable (fun x => ∑ i, A x i * B x i) (volume.restrict V) := by
      refine integrable_finsetSum _ fun i _ => ?_
      simpa only [Pi.mul_def] using (hA i).integrable_mul (hB i)
    simpa only [vecDot] using hsum
  obtain ⟨M, hM⟩ := hφb
  exact hpair.bdd_mul hφm (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact hM x)

end

end Homogenization.HighContrast.Multiscale
