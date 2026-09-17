import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage

/-!
# The restricted terminal optimizer and its subcell responses

The terminal-optimizer replacement of `p.response.transfer` restricts the optimizer of the terminal
cell to each aligned subcell of the coarse scale and compares the restricted response value there
with the subcell's own response.  The response integrand and the variation-energy integrand are
pointwise expressions in the coefficient and the gradient of the harmonic function, so restricting
the function to a subdomain leaves both integrands unchanged as functions.  Exact partition
averaging then expresses the terminal response value as the flat average of the restricted response
values over the aligned subcells; the entire scale defect therefore sits in the gap between each
subcell's own response and the restricted one.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Restricting a harmonic function to a subdomain leaves the scalar response integrand unchanged.
Both integrands are pointwise expressions in the coefficient and the gradient, and the restricted
harmonic function has the same gradient as the parent, so the two functions agree.  This is the
integrand identity used in the terminal-optimizer replacement of `p.response.transfer`. -/
theorem scalarResponseIntegrand_restrictOfIsEllipticFieldOn {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (p r : Vec d) (u : AHarmonicFunction a U) :
    scalarResponseIntegrand V a p r (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)
      = scalarResponseIntegrand U a p r u := by
  funext x
  have hgrad :
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simp only [scalarResponseIntegrand, hgrad]

/-- Restricting a harmonic function to a subdomain leaves the scalar variation-energy integrand
unchanged.  The integrand is a pointwise expression in the coefficient and the gradient, and the
restricted harmonic function has the same gradient as the parent.  This is the energy identity used
in the terminal-optimizer replacement of `p.response.transfer`. -/
theorem scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (u : AHarmonicFunction a U) :
    scalarVariationEnergyIntegrand a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)
      = scalarVariationEnergyIntegrand a u := by
  funext x
  have hgrad :
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simp only [scalarVariationEnergyIntegrand, hgrad]

/-- Exact partition averaging at a response maximizer: the flat average over the depth-`n` aligned
subcells of the parent response integrand is the parent response value, and at a maximizer that
value is the terminal response `J`.  Thus no response is lost in the subdivision; the entire scale
defect sits in the gap between each subcell's own response and the restricted one.  This is the
bookkeeping identity of the terminal-optimizer replacement of `p.response.transfer`. -/
theorem avsum_volumeAverage_scalarResponseIntegrand_eq_responseJ {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ) {a : CoeffField d} (p r : Vec d)
    (u : AHarmonicFunction a (HighContrast.adaptedCell q t))
    (hmax : IsResponseMaximizer (HighContrast.adaptedCell q t) p r a u)
    (hint : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (HighContrast.adaptedCell q t) a p r u) (HighContrast.adaptedCell q t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (scalarResponseIntegrand (HighContrast.adaptedCell q t) a p r u)
      = ResponseJ (HighContrast.adaptedCell q t) p r a := by
  rw [avsum_volumeAverage_eq q hq t n hint,
    ← responseJ_eq_of_isResponseMaximizer (HighContrast.adaptedCell q t) p r a hmax]

end

end Homogenization.HighContrast.Multiscale
