import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# Quadratic response: the difference energy is twice the response deficit

On a domain `V` carrying a pointwise elliptic coefficient `a`, let `v` be a
response maximizer for the load `(p, q)` and let `uV` be any other admissible
competitor (the restriction of a harmonic function from a larger set `U ⊇ V`).
Writing `X = (∇w, a ∇w)` for the doubled state of a field `w`, the quadratic
part of the response functional is exact at a maximizer: the first variation
vanishes, so the difference energy of the two states is

  `⨍_V (X_{uV} − X_v) · A (X_{uV} − X_v) = 4 (J(V) − ⨍_V g_V(uV))`

with `A` the pointwise block of `a` and `g_V` the response integrand.  Because
the pointwise block energy is twice the `symmPart` variation energy
(`X · A X = 2 ∇w · symmPart(a) ∇w`), this is equivalently the statement below:
the variation energy of the difference equals twice the response deficit.

The deficit is measured against the *value of the competitor on `V`*, not
against the parent-domain supremum `J(U)`: the two differ in general, since the
average of the parent integrand over a proper subset need not equal its average
over `U`.  The identity is the single-domain engine behind the recent-cell
response estimate; the recombination over a partition of `U` is a separate
step.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **Quadratic response on one domain pair.**  Let `V ⊆ U` be open sets, `a` be
pointwise elliptic on `V`, `v` a response maximizer on `V` for the load
`(p, q)`, and `u` any `a`-harmonic function on `U`.  Then the `symmPart`
variation energy on `V` of the difference between the restricted parent `u` and
the maximizer `v` is twice the response deficit of the restricted parent:

  `⨍_V (∇u − ∇v) · symmPart(a) (∇u − ∇v) = 2 (J(V) − ⨍_V g_V(u))`.

Only the maximizer on `V` is used; the parent need not be a maximizer on `U`.
The four integrability side conditions are those required by the first- and
second-variation identities. -/
theorem h6a_difference_energy_eq_response_deficit {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hU : IsOpen U) (hV : IsOpen V) [IsFiniteMeasure (volumeMeasureOn V)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam V a)
    {p q : Vec d} {u : AHarmonicFunction a U} {v : AHarmonicFunction a V}
    (hmaxV : IsResponseMaximizer V p q a v)
    (huV_int : weakFluxIntegrable V a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : IntegrableOn (scalarResponseIntegrand V a p q v) V)
    (hlin : IntegrableOn (scalarFirstVariationIntegrand V a p q v
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy : IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V) :
    volumeAverage V (fun x => vecDot
        ((u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad x - v.toH1.grad x)
        (matVecMul (symmPart (a x))
          ((u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad x - v.toH1.grad x))) =
      2 * (ResponseJ V p q a - volumeAverage V (scalarResponseIntegrand V a p q
          (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))) := by
  set uV : AHarmonicFunction a V := u.restrictOfIsEllipticFieldOn hU hV hVU hEll
    with huVdef
  set w : AHarmonicFunction a V :=
    AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1) with hwdef
  have hwgrad : ∀ x, w.toH1.grad x = uV.toH1.grad x - v.toH1.grad x := by
    intro x
    rw [hwdef, AHarmonicFunction.grad_addSMulOfIntegrable]
    simp [sub_eq_add_neg]
  have hw_int : weakFluxIntegrable V a w := by
    intro φ
    have h1 : IntegrableOn (fun x => vecDot (matVecMul (a x) (uV.toH1.grad x))
        (φ.toH1Function.grad x)) V := huV_int φ
    have h2 : IntegrableOn (fun x => vecDot (matVecMul (a x) (v.toH1.grad x))
        (φ.toH1Function.grad x)) V := hv_int φ
    have heq : (fun x => vecDot (matVecMul (a x) (w.toH1.grad x))
          (φ.toH1Function.grad x)) =
        fun x => vecDot (matVecMul (a x) (uV.toH1.grad x)) (φ.toH1Function.grad x) -
          vecDot (matVecMul (a x) (v.toH1.grad x)) (φ.toH1Function.grad x) := by
      funext x
      rw [hwgrad x, sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
        vecDot_neg_left]
      ring
    rw [heq]
    exact h1.sub h2
  have hsecond := responseJ_second_variation_line_of_isResponseMaximizer
    V a p q v hmaxV w 1 hv_int hw_int hresp_v hlin henergy
  have hpert : scalarResponseIntegrand V a p q (scalarPerturbation v w 1 hv_int hw_int) =
      scalarResponseIntegrand V a p q uV := by
    funext x
    have hg : (scalarPerturbation v w 1 hv_int hw_int).toH1.grad x = uV.toH1.grad x := by
      rw [scalarPerturbation_grad]
      simp only [Pi.add_apply, one_smul]
      rw [hwgrad x]
      abel
    simp only [scalarResponseIntegrand]
    rw [hg]
  rw [hpert] at hsecond
  have hE : volumeAverage V (scalarVariationEnergyIntegrand a w) =
      2 * (ResponseJ V p q a - volumeAverage V (scalarResponseIntegrand V a p q uV)) := by
    have h' : volumeAverage V (scalarResponseIntegrand V a p q uV) =
        ResponseJ V p q a - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a w) := by
      simpa using hsecond
    linarith [h']
  have hfun : scalarVariationEnergyIntegrand a w =
      fun x => vecDot (uV.toH1.grad x - v.toH1.grad x)
        (matVecMul (symmPart (a x)) (uV.toH1.grad x - v.toH1.grad x)) := by
    funext x
    simp only [scalarVariationEnergyIntegrand, hwgrad]
  rw [hfun] at hE
  rw [huVdef] at hE ⊢
  exact hE

end

end Homogenization.HighContrast.Multiscale
