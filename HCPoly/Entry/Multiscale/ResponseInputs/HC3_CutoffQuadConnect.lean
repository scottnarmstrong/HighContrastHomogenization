import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffQuadReadout

/-!
# The cutoff-weighted energy functional of the doubled minimizer

For a response cell `U`, a coefficient `a` lying on a quantitative ellipticity slice, and a cutoff
`φ`, the Hilbert `Mu` realization of `a` carries a continuous bilinear energy form.  Multiplying the
first argument pointwise by the cutoff and evaluating the energy on the diagonal gives the
functional `z ↦ ⨍_U φ ⟨z, B_a z⟩`, the cutoff-weighted energy of a doubled field.

The pointwise self-pairing of the canonical optimizer state is the doubled block energy of the
`Mu` minimizer plus twice the potential-flux pairing of the minimizer, so the quadratic term of the
expansion of the cutoff pairing `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)) is the value
at the minimizer of the sum of the cutoff-weighted energy and twice the cutoff-weighted
potential-flux readout.  This file records the continuity of that sum in the doubled field, the
analytic half of the measurability of the quadratic term.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The cutoff-weighted energy of a doubled field is continuous in the field.  The energy bilinear
form of the `Mu` realization is continuous, pointwise multiplication by the a.e. bounded cutoff is
continuous linear, and evaluation of a continuous linear functional is continuous.  This is the
analytic input to the cutoff-weighted quadratic term of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)). -/
theorem continuous_energyBilin_weightedBlockSMulL_self {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    Continuous fun z : HilbertBlockL2 U =>
      (responseCellMuHilbert hvol a).energyBilin
        (weightedBlockSMulL (U := U) hφm hφb z) z := by
  have hf : Continuous fun z : HilbertBlockL2 U =>
      (responseCellMuHilbert hvol a).energyBilin
        (weightedBlockSMulL (U := U) hφm hφb z) :=
    (responseCellMuHilbert hvol a).energyBilin.continuous.comp
      (weightedBlockSMulL (U := U) hφm hφb).continuous
  exact hf.clm_apply continuous_id

/-- The sum of the cutoff-weighted energy of a doubled field and twice its cutoff-weighted
potential-flux readout is continuous in the field.  Its value at the `Mu` minimizer is the
quadratic term of the expansion of the cutoff pairing `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)). -/
theorem continuous_weightedEnergy_add_cutoffQuadReadout {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    Continuous fun z : HilbertBlockL2 U =>
      (responseCellMuHilbert hvol a).energyBilin
          (weightedBlockSMulL (U := U) hφm hφb z) z
        + 2 * cutoffQuadReadout U φ z := by
  exact (continuous_energyBilin_weightedBlockSMulL_self hvol a hφm hφb).add
    (continuous_const.mul (continuous_cutoffQuadReadout U hvol hφm hφb))

end

end Homogenization.HighContrast.Multiscale
