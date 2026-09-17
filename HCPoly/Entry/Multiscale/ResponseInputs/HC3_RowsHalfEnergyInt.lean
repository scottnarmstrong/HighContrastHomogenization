import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyFam
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# Sample integrability of the cutoff half-energy defect

The centred cutoff decomposition of `p.response.transfer` integrates, against the law `P` of
coefficients, the difference between the cutoff-weighted half-energy of the terminal optimizer and
the terminal response.  A response cutoff keeps its weight between zero and two, so the
cutoff-weighted half-energy is dominated by the terminal energy, which at a maximizer is twice the
terminal response; the response is `P`-integrable and the weighted energy readout is measurable in
the sample, so that difference is `P`-integrable.

Both signs of the recentred coefficient, `a_- = a - g` and its adjoint twin `a_+ = aᵗ + g`, are
covered.

Paper: `p.response.transfer`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Sample integrability of the cutoff half-energy defect, minus sign.**  For a response cutoff
`φ` with `0 ≤ φ ≤ 2` and a terminal optimizer family for the recentred coefficient `a_-`, the
difference between the cutoff-weighted half-energy of the optimizer and the terminal response
`J_t^-` is `P`-integrable.  The half-energy is one half of the `φ`-weighted average of the terminal
energy density; its absolute value is at most twice the terminal response, since the terminal energy
average is twice the response and `|φ| ≤ 2`, so integrability follows by domination from the
`P`-integrability of the response. -/
theorem integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    MeasureTheory.Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hφabs : ∀ x : Vec d, ‖φ x‖ ≤ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hpt : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
        (optimizerField (respCoeffMinus F a) (uM a) x).2
      = scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffMinus F a x) ((uM a).toH1.grad x)).symm
  have hptfun : ∀ a : CoeffSpace d,
      (fun x : Vec d => φ x * vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
          (optimizerField (respCoeffMinus F a) (uM a) x).2)
        = fun x : Vec d => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x := by
    intro a
    funext x
    rw [hpt a x]
  have hEqFun : (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a))
      = fun a => (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) := by
    funext a
    simp only [cutoffHalfEnergyAux]
    rw [hptfun a]
  have hMeas : Measurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
      (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) :=
    measurable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e uM hmax
      hφm.aestronglyMeasurable (Filter.Eventually.of_forall hφabs)
  have hHalfInt : MeasureTheory.Integrable
      (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)) P := by
    rw [hEqFun]
    refine (hJt.const_mul 2).mono' ?_ ?_
    · exact (hMeas.const_mul (1 / 2)).aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_eq_abs]
      obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
        exists_elliptic_representative_respCell_respCoeffMinus (F := F) hjStar hm t a
      let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uM a)
      have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
          (respCell jStar F t) :=
        integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
      have hEae : scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)] scalarVariationEnergyIntegrand f v := by
        filter_upwards [hae] with x hx
        dsimp only [v]
        simp only [scalarVariationEnergyIntegrand, grad_aHarmonicFunctionOfAEEqCoeff]
        rw [hx]
      have hEf_nonneg_ae : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand f v :=
        (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx =>
          scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
            (respCell jStar F t) f hEll v x hx)
      have hE_nonneg : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) := by
        filter_upwards [hEae, hEf_nonneg_ae] with x hx hx0
        rw [hx]
        exact hx0
      have hF : IntegrableOn
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)
          (respCell jStar F t) := by
        refine ((hE.abs).const_mul 2).mono' ?_ ?_
        · exact (hφm.aestronglyMeasurable).mul hE.aestronglyMeasurable
        · filter_upwards with x
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hle : ∀ x ∈ respCell jStar F t,
          |φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
            ≤ 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := by
        intro x _hx
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hmain : |volumeAverage (respCell jStar F t)
            (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
          ≤ volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) :=
        volumeAverage_abs_le_of_le hU hle hF ((hE.abs).const_mul 2)
      have habs_eq : volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
          = volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
        unfold volumeAverage
        rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
      have h2 : volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
          = 2 * volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) := by
        simpa only [smul_eq_mul] using!
          volumeAverage_smul (respCell jStar F t) (2 : ℝ)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
      have hE_eq : volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
          = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a) :=
        volumeAverage_energy_respCell_respCoeffMinus_eq P jStar hjStar F hm t e uM hmax a
      calc |(1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
          = (1 / 2 : ℝ) * |volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
        _ ≤ (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) :=
              mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = (1 / 2 : ℝ) * (2 * volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)) := by
              rw [h2]
        _ = volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) := by ring
        _ = volumeAverage (respCell jStar F t)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := habs_eq
        _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a) := hE_eq
  exact hHalfInt.sub hJt

/-- **Sample integrability of the cutoff half-energy defect, plus sign.**  The twin of
`integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffMinus` for the adjoint recentred coefficient
`a_+ = aᵗ + g` and its terminal optimizer. -/
theorem integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    MeasureTheory.Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hφabs : ∀ x : Vec d, ‖φ x‖ ≤ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hpt : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
        (optimizerField (respCoeffPlus F a) (uP a) x).2
      = scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffPlus F a x) ((uP a).toH1.grad x)).symm
  have hptfun : ∀ a : CoeffSpace d,
      (fun x : Vec d => φ x * vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
          (optimizerField (respCoeffPlus F a) (uP a) x).2)
        = fun x : Vec d => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x := by
    intro a
    funext x
    rw [hpt a x]
  have hEqFun : (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a))
      = fun a => (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) := by
    funext a
    simp only [cutoffHalfEnergyAux]
    rw [hptfun a]
  have hMeas : Measurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
      (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) :=
    measurable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e uP hmax
      hφm.aestronglyMeasurable (Filter.Eventually.of_forall hφabs)
  have hHalfInt : MeasureTheory.Integrable
      (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)) P := by
    rw [hEqFun]
    refine (hJt.const_mul 2).mono' ?_ ?_
    · exact (hMeas.const_mul (1 / 2)).aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_eq_abs]
      obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
        exists_elliptic_representative_respCell_respCoeffPlus (F := F) hjStar hm t a
      let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uP a)
      have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
          (respCell jStar F t) :=
        integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
      have hEae : scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)] scalarVariationEnergyIntegrand f v := by
        filter_upwards [hae] with x hx
        dsimp only [v]
        simp only [scalarVariationEnergyIntegrand, grad_aHarmonicFunctionOfAEEqCoeff]
        rw [hx]
      have hEf_nonneg_ae : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand f v :=
        (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx =>
          scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
            (respCell jStar F t) f hEll v x hx)
      have hE_nonneg : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) := by
        filter_upwards [hEae, hEf_nonneg_ae] with x hx hx0
        rw [hx]
        exact hx0
      have hF : IntegrableOn
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
          (respCell jStar F t) := by
        refine ((hE.abs).const_mul 2).mono' ?_ ?_
        · exact (hφm.aestronglyMeasurable).mul hE.aestronglyMeasurable
        · filter_upwards with x
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hle : ∀ x ∈ respCell jStar F t,
          |φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
            ≤ 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := by
        intro x _hx
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hmain : |volumeAverage (respCell jStar F t)
            (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
          ≤ volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) :=
        volumeAverage_abs_le_of_le hU hle hF ((hE.abs).const_mul 2)
      have habs_eq : volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
          = volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
        unfold volumeAverage
        rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
      have h2 : volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
          = 2 * volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) := by
        simpa only [smul_eq_mul] using!
          volumeAverage_smul (respCell jStar F t) (2 : ℝ)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
      have hE_eq : volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
          = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a) :=
        volumeAverage_energy_respCell_respCoeffPlus_eq P jStar hjStar F hm t e uP hmax a
      calc |(1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
          = (1 / 2 : ℝ) * |volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
        _ ≤ (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) :=
              mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = (1 / 2 : ℝ) * (2 * volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)) := by
              rw [h2]
        _ = volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) := by ring
        _ = volumeAverage (respCell jStar F t)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := habs_eq
        _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a) := hE_eq
  exact hHalfInt.sub hJt

end

end Homogenization.HighContrast.Multiscale
