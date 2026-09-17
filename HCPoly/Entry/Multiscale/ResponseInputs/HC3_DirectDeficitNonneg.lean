import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRestrictResp

/-!
# Nonnegativity of the subcell deficit and of the subcell response

The terminal-optimizer replacement of `p.response.transfer` needs two signs.  First, restricting the
terminal optimizer to a subcell gives an admissible competitor there, so its response value on the
subcell is at most the subcell's own response: the deficit is nonnegative.  Second, the response of
a cell is nonnegative, because at a maximizer it is half the volume average of the nonnegative
variation-energy density of that maximizer.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit is nonnegative.**  Let `V ⊆ U` be open sets, `a` a coefficient elliptic
on `V`, and `v` a response maximizer on `V` for the load `(p, r)`.  Any `a`-harmonic function `u`
on `U`, restricted to the subcell `V`, is an admissible competitor there, so its response value on
`V` is at most the subcell response `J(V; p, r; a)`.  The restriction leaves the scalar response
integrand unchanged, so the deficit `J(V) - ⨍_V g_V(u)` is nonnegative.  This is the sign input of
the terminal-optimizer replacement of `p.response.transfer`. -/
theorem volumeAverage_scalarResponseIntegrand_le_responseJ {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (p r : Vec d) (u : AHarmonicFunction a U) (v : AHarmonicFunction a V)
    (hmax : IsResponseMaximizer V p r a v) :
    volumeAverage V (scalarResponseIntegrand U a p r u) ≤ ResponseJ V p r a := by
  have hcongr : volumeAverage V (scalarResponseIntegrand U a p r u)
      = volumeAverage V (scalarResponseIntegrand V a p r
          (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)) := by
    rw [scalarResponseIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll p r u]
  calc
    volumeAverage V (scalarResponseIntegrand U a p r u)
        = volumeAverage V (scalarResponseIntegrand V a p r
            (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)) := hcongr
    _ ≤ volumeAverage V (scalarResponseIntegrand V a p r v) :=
          hmax (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)
    _ = ResponseJ V p r a :=
          (responseJ_eq_of_isResponseMaximizer V p r a hmax).symm

/-- **The subcell response is nonnegative.**  Let `a` be a coefficient elliptic on `V` and `v` a
response maximizer on `V` for the load `(p, r)`.  At a maximizer the response equals half the
volume average of the variation-energy density of `v`, and that density is nonnegative for an
elliptic coefficient, so `J(V; p, r; a) ≥ 0`.  The side conditions are the integrability
hypotheses of the energy--response identity at the maximizer.  This is the sign input of the
terminal-optimizer replacement of `p.response.transfer`. -/
theorem responseJ_nonneg_of_isResponseMaximizer {d : ℕ} {V : Set (Vec d)}
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (p r : Vec d) (v : AHarmonicFunction a V) (hmax : IsResponseMaximizer V p r a v)
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : MeasureTheory.IntegrableOn (scalarResponseIntegrand V a p r v) V)
    (hlin_self : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand V a p r v v) V)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a v) V) :
    0 ≤ ResponseJ V p r a := by
  rw [responseJ_energy_of_isResponseMaximizer V a p r v hmax hv_int hresp_v hlin_self henergy]
  exact mul_nonneg (by norm_num)
    (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V a hEll v)

end

end Homogenization.HighContrast.Multiscale
