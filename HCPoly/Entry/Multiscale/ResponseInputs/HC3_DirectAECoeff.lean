import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeMaximizer
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The elliptic representative of a coefficient of the carrier

A point of the coefficient carrier is elliptic only almost everywhere, while the variational
identities of the response are stated for a pointwise elliptic coefficient.  The bridge is the
elliptic representative `aHarmonicFunctionOfAEEqCoeff`: replacing a coefficient by an almost
everywhere equal one carries a harmonic function along and leaves unchanged every quantity the
cutoff estimate of `p.response.transfer` mentions.  This module records that invariance for the
maximizer property, for the averaged variation energy on any measurable subset, and for the
cutoff half-energy.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The response-maximizer property is invariant under an almost-everywhere replacement of the
coefficient: if `u` maximizes the response functional for `a` on `U`, then the field carried
along `a =ᵐ b` maximizes it for `b`.  Both response averages are rewritten by
`volumeAverage_scalarResponseIntegrand_congr`; this is the transport behind the terminal-optimizer
replacement row of `p.response.transfer`. -/
theorem isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d)
    {u : AHarmonicFunction a U} (hmax : IsResponseMaximizer U p r a u) :
    IsResponseMaximizer U p r b (aHarmonicFunctionOfAEEqCoeff h u) := by
  intro w
  have key := hmax (aHarmonicFunctionOfAEEqCoeff h.symm w)
  have h1 : volumeAverage U (scalarResponseIntegrand U b p r w) =
      volumeAverage U (scalarResponseIntegrand U a p r
        (aHarmonicFunctionOfAEEqCoeff h.symm w)) :=
    volumeAverage_scalarResponseIntegrand_congr h.symm p r w _ (fun _ => rfl)
  have h2 : volumeAverage U (scalarResponseIntegrand U a p r u) =
      volumeAverage U (scalarResponseIntegrand U b p r (aHarmonicFunctionOfAEEqCoeff h u)) :=
    volumeAverage_scalarResponseIntegrand_congr h p r u _ (fun _ => rfl)
  rw [h1, ← h2]
  exact key

/-- Carrying a harmonic function across an almost-everywhere equality of coefficient fields
changes only the coefficient field, not the underlying `H1Function`: the two gradients are equal
on the nose. -/
theorem grad_aHarmonicFunctionOfAEEqCoeff {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (u : AHarmonicFunction a U) :
    (aHarmonicFunctionOfAEEqCoeff h u).toH1.grad = u.toH1.grad := rfl

/-- The averaged variation energy on a smaller measurable set is invariant under an
almost-everywhere replacement of the coefficient: `a` and `b` agree almost everywhere on `U`,
hence on any `V ⊆ U`, and the two energy integrands differ only through the coefficient matrix
there. -/
theorem volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff {d : ℕ}
    {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b)
    (u : AHarmonicFunction a U) :
    volumeAverage V (scalarVariationEnergyIntegrand b (aHarmonicFunctionOfAEEqCoeff h u))
      = volumeAverage V (scalarVariationEnergyIntegrand a u) := by
  have hV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hV] with x hx
  simp only [scalarVariationEnergyIntegrand, grad_aHarmonicFunctionOfAEEqCoeff, ← hx]

/-- The cutoff half-energy is invariant under an almost-everywhere replacement of the
coefficient: the doubled optimizer state `X = (∇u, b ∇u)` agrees wherever `a = b`, so its
cutoff-weighted half-energy is unchanged. -/
theorem cutoffHalfEnergyAux_aHarmonicFunctionOfAEEqCoeff {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b) (φ : Vec d → ℝ)
    (u : AHarmonicFunction a U) :
    cutoffHalfEnergyAux U φ b (aHarmonicFunctionOfAEEqCoeff h u) = cutoffHalfEnergyAux U φ a u := by
  unfold cutoffHalfEnergyAux volumeAverage
  congr 1
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp only [optimizerField, grad_aHarmonicFunctionOfAEEqCoeff, ← hx]

end

end Homogenization.HighContrast.Multiscale
