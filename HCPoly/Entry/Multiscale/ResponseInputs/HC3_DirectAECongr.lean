import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECoeff

/-!
# The congruence toolbox of the almost-everywhere elliptic representative

A point of the coefficient carrier is elliptic only almost everywhere, while the variational
identities of the response are stated for a pointwise elliptic coefficient.  The elliptic
representative supplies, for each sample, a pointwise elliptic field agreeing almost everywhere
with the carrier coefficient on the parent domain, and `aHarmonicFunctionOfAEEqCoeff` carries a
harmonic function along that replacement.  This module records the invariances the first error row
of `p.response.transfer` still needs: restriction of ellipticity to a measurable subset,
invariance of `ResponseJ` on a subset, the averaged response and the `ψ`-weighted variation energy
of a carried-along harmonic function, and the transport of their `IntegrableOn` facts.
-/

open Homogenization.HighContrast.CG

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Ellipticity restricts to a measurable subset. -/
theorem isEllipticFieldOn_subset {d : ℕ} {lam Lam : ℝ} {U V : Set (Vec d)} {f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U f) (hVU : V ⊆ U) (hV : MeasurableSet V) :
    IsEllipticFieldOn lam Lam V f :=
  IsEllipticFieldOn.mono hEll hV hVU

/-- The response `ResponseJ` on a subset is unchanged by an almost-everywhere replacement of the
coefficient on the parent. -/
theorem responseJ_congr_of_ae_eq_subset {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d) :
    ResponseJ V p r a = ResponseJ V p r b := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  exact responseJ_congr_of_ae_eq habV p r

/-- The averaged response integrand of a carried-along harmonic function, on a subset. -/
theorem volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff {d : ℕ}
    {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d) (u : AHarmonicFunction a U) :
    volumeAverage V (scalarResponseIntegrand U b p r (aHarmonicFunctionOfAEEqCoeff h u))
      = volumeAverage V (scalarResponseIntegrand U a p r u) := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [habV] with x hx
  simp only [scalarResponseIntegrand, grad_aHarmonicFunctionOfAEEqCoeff, ← hx]

/-- The averaged `ψ`-weighted variation energy of a carried-along harmonic function, on a subset:
weighting by an arbitrary scalar function changes nothing in the transport. -/
theorem volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
    {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (ψ : Vec d → ℝ) (u : AHarmonicFunction a U) :
    volumeAverage V (fun x => ψ x *
        scalarVariationEnergyIntegrand b (aHarmonicFunctionOfAEEqCoeff h u) x)
      = volumeAverage V (fun x => ψ x * scalarVariationEnergyIntegrand a u x) := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [habV] with x hx
  simp only [scalarVariationEnergyIntegrand, grad_aHarmonicFunctionOfAEEqCoeff, ← hx]

/-- An `IntegrableOn` fact transports across the carried-along harmonic function, for the
response integrand of the parent, restricted to a subset. -/
theorem integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff {d : ℕ}
    {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d) (u : AHarmonicFunction a U)
    (hint : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p r u) V) :
    MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U b p r (aHarmonicFunctionOfAEEqCoeff h u)) V := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  have hcongr :
      (scalarResponseIntegrand U a p r u)
        =ᵐ[volumeMeasureOn V]
      (scalarResponseIntegrand U b p r (aHarmonicFunctionOfAEEqCoeff h u)) := by
    filter_upwards [habV] with x hx
    simp only [scalarResponseIntegrand, grad_aHarmonicFunctionOfAEEqCoeff, ← hx]
  exact hint.congr hcongr

end

end Homogenization.HighContrast.Multiscale
