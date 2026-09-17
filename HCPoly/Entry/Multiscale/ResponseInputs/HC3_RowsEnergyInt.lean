import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyIdent
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsSumDom
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPairing
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRowsPhiFluct

/-!
# Sample integrability of the subcell and weighted optimizer energies

The terminal-optimizer replacement row of `p.response.transfer` needs, for each aligned subcell of
the coarse scale, the sample integrability of the subcell average of the terminal optimizer's
energy density, and the sample integrability of the `(φ - 1)`-weighted terminal energy.  Both are
obtained by domination.  The subcell energies are nonnegative and their flat average is the
terminal cell energy, which at a maximizer is twice the terminal response; and the cutoff satisfies
`|φ - 1| ≤ 1`, so the weighted terminal energy is dominated by the terminal energy, itself twice the
response.  The four statements below are the two signs of each fact, for the recentred coefficient
`a_- = a - g` and its adjoint twin `a_+ = aᵗ + g`.

Paper: `p.response.transfer`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Sample integrability of the subcell energy, minus sign.**  On every aligned subcell of the
coarse scale the average of the terminal optimizer energy density is `P`-integrable, because that
average is nonnegative and the flat sum of the subcell averages equals the terminal cell average,
which at a maximizer is twice the terminal response `J_t^-`; the response is `P`-integrable and each
subcell average is `P`-a.e.-strongly measurable. -/
theorem integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P) :
    ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := by
  have hcard : (((triadicIndexBox d H).card : ℝ)) ≠ 0 := by
    rw [card_triadicIndexBox]
    exact ne_of_gt (by positivity)
  refine fun w hw => integrable_of_nonneg_of_sum_eq
    (Z := triadicIndexBox d H)
    (f := fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
    (g := fun a => ((triadicIndexBox d H).card : ℝ) *
      (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)))
    ?_ ?_ ?_ ?_ w hw
  · intro i hi a
    exact zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus
      jStar hjStar F hm H s t ht uM a i hi
  · exact hmeasE
  · simpa only [mul_assoc] using hJt.const_mul (((triadicIndexBox d H).card : ℝ) * 2)
  · intro a
    have h1 := avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus_eq
      jStar hjStar F hm H s t ht uM a
    have h2 := volumeAverage_energy_respCell_respCoeffMinus_eq P jStar hjStar F hm t e uM hmax a
    rw [h2] at h1
    calc ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
        = 1 * (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) := (one_mul _).symm
      _ = (((triadicIndexBox d H).card : ℝ) * (((triadicIndexBox d H).card : ℝ))⁻¹) *
            (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) := by
            rw [mul_inv_cancel₀ hcard]
      _ = ((triadicIndexBox d H).card : ℝ) *
            ((((triadicIndexBox d H).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) := by
            rw [mul_assoc]
      _ = ((triadicIndexBox d H).card : ℝ) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)) := by
            rw [h1]

/-- **Sample integrability of the weighted terminal energy, minus sign.**  For a response cutoff
`φ` with `0 ≤ φ ≤ 2`, the `(φ - 1)`-weighted terminal optimizer energy is `P`-integrable: its
absolute value is at most the terminal energy average, which at a maximizer is twice the terminal
response `J_t^-`, and the response is `P`-integrable. -/
theorem integrable_volumeAverage_weighted_energy_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P) :
    MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  refine (hJt.const_mul 2).mono' hmeasW ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uM a)
  have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      (respCell jStar F t) :=
    integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
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
  have hF : IntegrableOn (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) (respCell jStar F t) := by
    refine (hE.abs).mono' ?_ ?_
    · exact ((hφm.sub measurable_const).aestronglyMeasurable).mul hE.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
          ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| :=
            mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
        _ = |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := one_mul _
  have hle : ∀ x ∈ respCell jStar F t,
      |(φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
        ≤ |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := by
    intro x _hx
    rw [abs_mul]
    calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
        ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| :=
          mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
      _ = |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := one_mul _
  have hmain : |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) :=
    volumeAverage_abs_le_of_le hU hle hF hE.abs
  have habs_eq : volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
      = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
    unfold volumeAverage
    rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
  have hE_eq : volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) :=
    volumeAverage_energy_respCell_respCoeffMinus_eq P jStar hjStar F hm t e uM hmax a
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) := hmain
    _ = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := habs_eq
    _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := hE_eq

/-- **Sample integrability of the subcell energy, plus sign.**  The twin of
`integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus` for the adjoint recentred
coefficient `a_+ = aᵗ + g` and its terminal optimizer. -/
theorem integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P) :
    ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := by
  have hcard : (((triadicIndexBox d H).card : ℝ)) ≠ 0 := by
    rw [card_triadicIndexBox]
    exact ne_of_gt (by positivity)
  refine fun w hw => integrable_of_nonneg_of_sum_eq
    (Z := triadicIndexBox d H)
    (f := fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
    (g := fun a => ((triadicIndexBox d H).card : ℝ) *
      (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)))
    ?_ ?_ ?_ ?_ w hw
  · intro i hi a
    exact zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus
      jStar hjStar F hm H s t ht uP a i hi
  · exact hmeasE
  · simpa only [mul_assoc] using hJt.const_mul (((triadicIndexBox d H).card : ℝ) * 2)
  · intro a
    have h1 := avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus_eq
      jStar hjStar F hm H s t ht uP a
    have h2 := volumeAverage_energy_respCell_respCoeffPlus_eq P jStar hjStar F hm t e uP hmax a
    rw [h2] at h1
    calc ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
        = 1 * (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) := (one_mul _).symm
      _ = (((triadicIndexBox d H).card : ℝ) * (((triadicIndexBox d H).card : ℝ))⁻¹) *
            (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) := by
            rw [mul_inv_cancel₀ hcard]
      _ = ((triadicIndexBox d H).card : ℝ) *
            ((((triadicIndexBox d H).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) := by
            rw [mul_assoc]
      _ = ((triadicIndexBox d H).card : ℝ) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)) := by
            rw [h1]

/-- **Sample integrability of the weighted terminal energy, plus sign.**  The twin of
`integrable_volumeAverage_weighted_energy_respCoeffMinus` for the adjoint recentred coefficient
`a_+ = aᵗ + g`. -/
theorem integrable_volumeAverage_weighted_energy_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P) :
    MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  refine (hJt.const_mul 2).mono' hmeasW ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae (uP a)
  have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      (respCell jStar F t) :=
    integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
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
  have hF : IntegrableOn (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) (respCell jStar F t) := by
    refine (hE.abs).mono' ?_ ?_
    · exact ((hφm.sub measurable_const).aestronglyMeasurable).mul hE.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
          ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| :=
            mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
        _ = |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := one_mul _
  have hle : ∀ x ∈ respCell jStar F t,
      |(φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
        ≤ |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := by
    intro x _hx
    rw [abs_mul]
    calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
        ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| :=
          mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
      _ = |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := one_mul _
  have hmain : |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) :=
    volumeAverage_abs_le_of_le hU hle hF hE.abs
  have habs_eq : volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
      = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
    unfold volumeAverage
    rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
  have hE_eq : volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) :=
    volumeAverage_energy_respCell_respCoeffPlus_eq P jStar hjStar F hm t e uP hmax a
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) := hmain
    _ = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := habs_eq
    _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := hE_eq

end

end Homogenization.HighContrast.Multiscale
