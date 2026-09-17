import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECongr
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectSubcellDeficit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectDeficitNonneg
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# The subcell comparison at an almost-everywhere elliptic coefficient

`HC3_DirectSubcellDeficit.abs_half_energy_adaptedCellAtCenter_sub_responseJ_le` proves, for a pointwise
elliptic coefficient `b` on the terminal cell and any `b`-harmonic `u` there, the subcell comparison

  `|½ ⨍_V g_b(u) − J(V)| ≤ D + 2√(J(V)·D)`,  `D = J(V) − ⨍_V g_U(u)`,

on each aligned subcell `V = adaptedCellAtCenter q (t−n) w`.  The response coefficients
`respCoeff∓ F a` are elliptic only almost everywhere, so this module runs that estimate at a
pointwise elliptic representative and transports every quantity back across the a.e. replacement,
which leaves each of them invariant.  It also records the two nonnegativities the row assembly
needs: `0 ≤ J(V)` and `0 ≤ D`.
-/

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The transport core of the subcell comparison: given a pointwise elliptic representative `f`
of a coefficient `b` on the terminal cell, the comparison holds for `b` itself. -/
private theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_of_aeRep {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand b u)
        - ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b|
      ≤ (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
          - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))
        + 2 * Real.sqrt
            (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
              * (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
                - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))) := by
  have hU : IsOpen (HighContrast.adaptedCell q t) := isOpen_adaptedCell_of_isUnit hq t
  have hV : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    hEll.mono hV.measurableSet hVU
  set v : AHarmonicFunction f (HighContrast.adaptedCell q t) := aHarmonicFunctionOfAEEqCoeff hae u
    with hv
  have hmain := abs_half_energy_adaptedCellAtCenter_sub_responseJ_le hq t n hEll p r v hw (by
    intro hfin vv' hvv'max
    have : MeasureTheory.IsFiniteMeasure
        (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := hfin
    have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
    have huV_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f
        (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV) :=
      hdata.weakFlux (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
    have hv_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f vv' :=
      hdata.weakFlux vv'
    have henergy_u : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand f v)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
      rw [← scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEllV v]
      exact hdata.energy (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
    have hgradpar :
        (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV).toH1.grad = v.toH1.grad := by
      rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
      simp only [H1Function.restrict]
    have hcross : MeasureTheory.IntegrableOn
        (fun x => vecDot (vv'.toH1.grad x)
          (matVecMul (symmPart (f x)) (v.toH1.grad x - vv'.toH1.grad x)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
      have h1 := hdata.cross (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV) vv'
      have h2 := hdata.cross vv' vv'
      refine (h1.sub h2).congr ?_
      filter_upwards with x
      rw [hgradpar]
      simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right,
        vecDot_neg_right, Pi.add_apply, Pi.neg_apply]
    exact abs_half_energy_sub_responseJ_le_deficit hU hV hVU hEllV v vv' hvv'max
      huV_int hv_int (hdata.response p r vv') (hdata.firstVariation p r vv' vv')
      (hdata.energy vv')
      (hdata.firstVariation p r vv'
        (AHarmonicFunction.addSMulOfIntegrable (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
          vv' huV_int hv_int (-1)))
      (hdata.energy
        (AHarmonicFunction.addSMulOfIntegrable (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
          vv' huV_int hv_int (-1)))
      henergy_u hcross)
  have hEnergy : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarVariationEnergyIntegrand f v)
      = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarVariationEnergyIntegrand b u) := by
    rw [hv]
    exact volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae u
  have hResp : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) f p r v)
      = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) := by
    rw [hv]
    exact volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae p r u
  have hJ : ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
      = ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b :=
    (responseJ_congr_of_ae_eq_subset hVU hae p r).symm
  simpa only [hEnergy, hJ, hResp] using hmain

/-- The transport core of the two signs: given a pointwise elliptic representative `f` of a
coefficient `b` on the terminal cell, the subcell response and the subcell deficit for `b` are
nonnegative. -/
private theorem responseJ_nonneg_and_deficit_nonneg_of_aeRep {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    0 ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
      ∧ 0 ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
            - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) := by
  have hU : IsOpen (HighContrast.adaptedCell q t) := isOpen_adaptedCell_of_isUnit hq t
  have hV : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w
  have hne : (adaptedCellAtCenter q (t - (n : ℤ)) w).Nonempty := by
    obtain ⟨z, hz⟩ := adaptedCell_nonempty q (t - (n : ℤ))
    exact ⟨adaptedCellCenter q (t - (n : ℤ)) w + z, z, hz, rfl⟩
  have : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using hdom.isFiniteMeasure_restrict_volume
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    hEll.mono hV.measurableSet hVU
  set v : AHarmonicFunction f (HighContrast.adaptedCell q t) := aHarmonicFunctionOfAEEqCoeff hae u
    with hv
  obtain ⟨vmax⟩ :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEllV p r
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  have hJf : 0 ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f :=
    responseJ_nonneg_of_isResponseMaximizer hEllV p r
      (vmax : AHarmonicFunction f (adaptedCellAtCenter q (t - (n : ℤ)) w)) vmax.isResponseMaximizer
      (hdata.weakFlux vmax) (hdata.response p r vmax)
      (hdata.firstVariation p r vmax vmax) (hdata.energy vmax)
  have hlef : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) f p r v)
      ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f :=
    volumeAverage_scalarResponseIntegrand_le_responseJ hU hV hVU hEllV p r v
      (vmax : AHarmonicFunction f (adaptedCellAtCenter q (t - (n : ℤ)) w)) vmax.isResponseMaximizer
  constructor
  · rw [responseJ_congr_of_ae_eq_subset hVU hae p r]
    exact hJf
  · rw [responseJ_congr_of_ae_eq_subset hVU hae p r,
      ← volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae p r u]
    rw [hv] at hlef
    linarith

/-- The subcell comparison on an aligned adapted subcell, for the minus family, with no
pointwise ellipticity hypothesis. -/
theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffMinus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) u)
        - ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
            (respCoeffMinus F a)|
      ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r u))
        + 2 * Real.sqrt
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                (respCoeffMinus F a)
              * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                    (respCoeffMinus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r u))) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  exact abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

/-- The subcell comparison on an aligned adapted subcell, for the plus family, with no pointwise
ellipticity hypothesis. -/
theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffPlus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) u)
        - ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
            (respCoeffPlus F a)|
      ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r u))
        + 2 * Real.sqrt
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                (respCoeffPlus F a)
              * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                    (respCoeffPlus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r u))) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  exact abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

/-- Nonnegativity of the subcell response and of the subcell deficit, minus family. -/
theorem responseJ_nonneg_and_deficit_nonneg_respCoeffMinus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffMinus F a)
      ∧ 0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
              (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r u) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  exact responseJ_nonneg_and_deficit_nonneg_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

/-- Nonnegativity of the subcell response and of the subcell deficit, plus family. -/
theorem responseJ_nonneg_and_deficit_nonneg_respCoeffPlus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffPlus F a)
      ∧ 0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
              (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r u) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  exact responseJ_nonneg_and_deficit_nonneg_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

end

end Homogenization.HighContrast.Multiscale
