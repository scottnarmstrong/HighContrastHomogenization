import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellCS
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRestrictResp
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakQuadraticResponse

/-!
# The subcell response deficit controls the terminal optimizer's energy

The terminal-optimizer replacement of `p.response.transfer` compares the energy of the terminal
optimizer with the subcell responses.  Let `V ⊆ U`, let `u` optimize the response problem on the
large cell `U`, and let `v` optimize the same load on the small cell `V`.  Restricted to `V`, `u`
is an admissible competitor there, so its response value on `V` falls short of `J(V)` by the
nonnegative deficit

  `D = J(V) - ⨍_V g_V(u)`.

The quadratic-response identity makes the `symmPart(a)`-energy of `∇u - ∇v` on `V` exactly `2 D`.
Splitting the two energies and bounding the cross term by Cauchy--Schwarz against
`⨍_V ⟨∇v, symmPart(a) ∇v⟩ = 2 J(V)` bounds the terminal optimizer's energy against the subcell
response:

  `|½ ⨍_V ⟨∇u, symmPart(a) ∇u⟩ - J(V)| ≤ D + 2 √(J(V) · D)`.

This is the pathwise engine of the terminal-optimizer replacement of `p.response.transfer`.

Paper: `p.response.transfer`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit controls the terminal optimizer's energy.**  Let `V ⊆ U` be open sets,
`a` a coefficient elliptic on `V`, `v` a response maximizer on `V` for the load `(p, r)`, and `u`
any `a`-harmonic function on `U`.  Writing `J = J(V; p, r; a)` for the subcell response and
`D = J - ⨍_V g_V(u)` for the deficit of the restricted parent `u` against it, the terminal
optimizer's energy on `V` is controlled by the subcell response through

  `|½ ⨍_V ⟨∇u, symmPart(a) ∇u⟩ - J| ≤ D + 2 √(J · D)`.

The difference energy of `∇u - ∇v` is `2 D` by the quadratic-response identity, and the cross
term `⨍_V ⟨∇v, symmPart(a)(∇u - ∇v)⟩` is bounded by averaged Cauchy--Schwarz against the two
diagonal energies `2 J` and `2 D`.  The side conditions are the integrability hypotheses of the
difference-energy identity, the energy--response identity at `v`, the cross integrability, and the
parent's energy integrability. -/
theorem abs_half_energy_sub_responseJ_le_deficit {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    {p r : Vec d} (u : AHarmonicFunction a U) (v : AHarmonicFunction a V)
    (hmax : IsResponseMaximizer V p r a v)
    (huV_int : weakFluxIntegrable V a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : MeasureTheory.IntegrableOn (scalarResponseIntegrand V a p r v) V)
    (hlin_vv : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand V a p r v v) V)
    (henergy_v : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a v) V)
    (hlin_diff : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand V a p r v
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy_diff : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy_u : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) V)
    (hcross : MeasureTheory.IntegrableOn (fun x => vecDot (v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) V) :
    |(1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u) - ResponseJ V p r a|
      ≤ (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
        + 2 * Real.sqrt (ResponseJ V p r a
            * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
  set uV : AHarmonicFunction a V := u.restrictOfIsEllipticFieldOn hU hV hVU hEll with huVdef
  -- The restricted optimizer has the same gradient as its parent.
  have hgrad : (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  have hgradV : uV.toH1.grad = u.toH1.grad := by
    rw [huVdef]
    exact hgrad
  -- The deficit energy: `⨍_V ⟨∇u - ∇v, symmPart(a)(∇u - ∇v)⟩ = 2 D`.
  have hdelta : volumeAverage V (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
      = 2 * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u)) := by
    have h6 := h6a_difference_energy_eq_response_deficit hVU hU hV hEll hmax huV_int hv_int
      hresp_v hlin_diff henergy_diff
    rw [scalarResponseIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll p r u] at h6
    rw [hgrad] at h6
    exact h6
  -- The difference integrand is the variation energy of the perturbation `uV - v`.
  have hwgrad : (AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)).toH1.grad
      = fun x => u.toH1.grad x - v.toH1.grad x := by
    rw [AHarmonicFunction.grad_addSMulOfIntegrable]
    funext x i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [congrFun hgradV x]
    ring
  have hSdxs_eq : (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
      = scalarVariationEnergyIntegrand a
          (AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)) := by
    funext x
    simp only [scalarVariationEnergyIntegrand]
    rw [congrFun hwgrad x]
  have hSdxs_int : IntegrableOn (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) V := by
    rw [hSdxs_eq]
    exact henergy_diff
  -- The energy--response identity at the subcell maximizer.
  have hJ : ResponseJ V p r a
      = (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a v) :=
    responseJ_energy_of_isResponseMaximizer V a p r v hmax hv_int hresp_v hlin_vv henergy_v
  -- Pointwise splitting of the two energies.
  have hpoint : ∀ x, scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x
      = vecDot (u.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))
        + 2 * vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)) := by
    intro x
    have hcomm := vecDot_matVecMul_symmPart_comm (a x) (u.toH1.grad x) (v.toH1.grad x)
    simp only [scalarVariationEnergyIntegrand, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
      vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hcomm]
    ring
  -- Averaging the pointwise splitting.
  have h2cross_int : IntegrableOn ((2 : ℝ) • (fun x => vecDot (v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))) V := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hcross.const_mul (2 : ℝ)
  have hfun : (fun x => scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x)
      = (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
        + (2 : ℝ) • (fun x => vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
    funext x
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hpoint x
  have hsub : volumeAverage V (fun x => scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x)
      = volumeAverage V (scalarVariationEnergyIntegrand a u)
        - volumeAverage V (scalarVariationEnergyIntegrand a v) :=
    volumeAverage_sub henergy_u henergy_v
  have havg : volumeAverage V (fun x => scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x)
      = volumeAverage V (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
        + 2 * volumeAverage V (fun x => vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
    rw [hfun, volumeAverage_add hSdxs_int h2cross_int,
      volumeAverage_smul V (2 : ℝ) (fun x => vecDot (v.toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))]
  -- The terminal energy differs from `J` by the deficit plus the cross average.
  have hmain : (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
        - ResponseJ V p r a
      = (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
        + volumeAverage V (fun x => vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
    calc
      (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
          - ResponseJ V p r a
          = (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
            - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a v) := by rw [hJ]
      _ = (1 / 2 : ℝ) * (volumeAverage V (scalarVariationEnergyIntegrand a u)
            - volumeAverage V (scalarVariationEnergyIntegrand a v)) := by ring
      _ = (1 / 2 : ℝ) * volumeAverage V (fun x => scalarVariationEnergyIntegrand a u x
            - scalarVariationEnergyIntegrand a v x) := by rw [hsub]
      _ = (1 / 2 : ℝ) * (volumeAverage V (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
            + 2 * volumeAverage V (fun x => vecDot (v.toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))) := by rw [havg]
      _ = (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
            + volumeAverage V (fun x => vecDot (v.toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
            rw [hdelta]
            ring
  -- Nonnegativity of the two quantities under the square roots.
  have hJnonneg : 0 ≤ ResponseJ V p r a := by
    have hA := volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V a hEll v
    rw [hJ]
    exact mul_nonneg (by norm_num) hA
  have hDnonneg : 0 ≤ ResponseJ V p r a
      - volumeAverage V (scalarResponseIntegrand U a p r u) := by
    have hle := hmax uV
    have hJuV' : volumeAverage V (scalarResponseIntegrand V a p r
          (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
        = volumeAverage V (scalarResponseIntegrand U a p r u) := by
      rw [scalarResponseIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll p r u]
    have hJuV : volumeAverage V (scalarResponseIntegrand V a p r uV)
        = volumeAverage V (scalarResponseIntegrand U a p r u) := by
      rw [huVdef]
      exact hJuV'
    have hJv := responseJ_eq_of_isResponseMaximizer V p r a hmax
    linarith [hle, hJuV, hJv]
  -- Cauchy--Schwarz for the cross term.
  have hcs0 := abs_volumeAverage_vecDot_symmPart_le (U := V) (a := a) hV.measurableSet hEll
    v.toH1.grad (fun x => u.toH1.grad x - v.toH1.grad x)
    (by simpa only [scalarVariationEnergyIntegrand] using! henergy_v)
    hSdxs_int hcross
  have hEv : volumeAverage V (fun x => vecDot (v.toH1.grad x)
        (matVecMul (symmPart (a x)) (v.toH1.grad x))) = 2 * ResponseJ V p r a := by
    have h' : volumeAverage V (scalarVariationEnergyIntegrand a v)
        = 2 * ResponseJ V p r a := by linarith [hJ]
    simpa only [scalarVariationEnergyIntegrand] using! h'
  have hcs : |volumeAverage V (fun x => vecDot (v.toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))|
      ≤ 2 * Real.sqrt (ResponseJ V p r a
          * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
    have h := hcs0
    rw [hEv, hdelta] at h
    have hsqrt : Real.sqrt (2 * ResponseJ V p r a)
          * Real.sqrt (2 * (ResponseJ V p r a
            - volumeAverage V (scalarResponseIntegrand U a p r u)))
        = 2 * Real.sqrt (ResponseJ V p r a
            * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
      calc
        Real.sqrt (2 * ResponseJ V p r a) * Real.sqrt (2 * (ResponseJ V p r a
              - volumeAverage V (scalarResponseIntegrand U a p r u)))
            = (Real.sqrt 2 * Real.sqrt (ResponseJ V p r a))
              * (Real.sqrt 2 * Real.sqrt (ResponseJ V p r a
                - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
                Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.sqrt (ResponseJ V p r a)
                * Real.sqrt (ResponseJ V p r a
                  - volumeAverage V (scalarResponseIntegrand U a p r u))) := by ring
        _ = 2 * (Real.sqrt (ResponseJ V p r a)
              * Real.sqrt (ResponseJ V p r a
                - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
              rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        _ = 2 * Real.sqrt (ResponseJ V p r a
              * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
              rw [Real.sqrt_mul hJnonneg]
    rw [hsqrt] at h
    exact h
  calc
    |(1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
        - ResponseJ V p r a|
        = |(ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
            + volumeAverage V (fun x => vecDot (v.toH1.grad x)
              (matVecMul (symmPart (a x))
                (u.toH1.grad x - v.toH1.grad x)))| := by rw [hmain]
    _ ≤ |ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u)|
          + |volumeAverage V (fun x => vecDot (v.toH1.grad x)
              (matVecMul (symmPart (a x))
                (u.toH1.grad x - v.toH1.grad x)))| := abs_add_le _ _
    _ = (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
          + |volumeAverage V (fun x => vecDot (v.toH1.grad x)
              (matVecMul (symmPart (a x))
                (u.toH1.grad x - v.toH1.grad x)))| := by rw [abs_of_nonneg hDnonneg]
    _ ≤ (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
          + 2 * Real.sqrt (ResponseJ V p r a
              * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
          linarith [hcs]

end

end Homogenization.HighContrast.Multiscale
