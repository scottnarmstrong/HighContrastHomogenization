import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyFam
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyIdent
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeMaximizer
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# The subcell energy of the terminal optimizer is measurable in the sample

The weighted energy readout of the terminal optimizer of `p.response.transfer` is measurable in the
coefficient sample for every weight bounded by two.  Taking the weight to be the indicator of an
aligned subcell turns the terminal-cell average into the subcell average, up to the constant ratio
of the two volumes; hence the subcell average of the energy density of the terminal optimizer is
measurable in the sample, for an arbitrary family of terminal maximizers.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The terminal-cell average of a function weighted by the indicator of a measurable subcell is
the ratio of the two volumes times the subcell average of that function. -/
private theorem volumeAverage_indicator_mul {d : ℕ} {U V : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ U) (hVvol : (volume V).toReal ≠ 0) (f : Vec d → ℝ) :
    volumeAverage U (fun x => V.indicator (fun _ : Vec d => (1 : ℝ)) x * f x)
      = ((volume V).toReal / (volume U).toReal) * volumeAverage V f := by
  have hfun : (fun x => V.indicator (fun _ : Vec d => (1 : ℝ)) x * f x) = V.indicator f := by
    funext x
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hint : ∫ x in U, V.indicator f x = ∫ x in V, f x := by
    rw [MeasureTheory.setIntegral_indicator hV, Set.inter_eq_self_of_subset_right hVU]
  rw [volumeAverage, hfun, hint, volumeAverage]
  field_simp

/-- **The subcell energy of the terminal optimizer is measurable in the sample, minus sign.**  For
every aligned subcell of the coarse scale, the subcell average of the energy density of the
terminal optimizer of the recentred coefficient `a_- = a - g` is a measurable function of the
coefficient sample, for an arbitrary family of terminal maximizers. -/
theorem measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  set eta : Vec d → ℝ := (adaptedCellAtCenter (respGrid jStar F) s w).indicator
    (fun _ : Vec d => (1 : ℝ)) with heta
  have hetam : AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)) :=
    (measurable_const.indicator hVmeas).aestronglyMeasurable
  have hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2 := by
    filter_upwards with x
    by_cases hx : x ∈ adaptedCellAtCenter (respGrid jStar F) s w
    · simp only [heta, Set.indicator_of_mem hx, norm_one]
      norm_num
    · simp only [heta, Set.indicator_of_notMem hx, norm_zero]
      norm_num
  have hmeas := measurable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e
    uM hmax (eta := eta) hetam hetab
  have hVpos : 0 < (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq s w
  set c : ℝ := (volume (respCell jStar F t)).toReal /
    (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal with hc
  have hkey : (fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      = fun a : CoeffSpace d => c * volumeAverage (respCell jStar F t)
          (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) := by
    funext a
    rw [volumeAverage_indicator_mul hVmeas hVU (ne_of_gt hVpos)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))]
    have hUpos : 0 < (volume (respCell jStar F t)).toReal := by
      simpa only [respCell] using adaptedCell_volume_toReal_pos (respGrid jStar F) hq t
    rw [hc]
    field_simp
  rw [hkey]
  exact hmeas.const_mul c

/-- **The subcell energy of the terminal optimizer is measurable in the sample, plus sign.**  The
adjoint twin of `measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus`. -/
theorem measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  set eta : Vec d → ℝ := (adaptedCellAtCenter (respGrid jStar F) s w).indicator
    (fun _ : Vec d => (1 : ℝ)) with heta
  have hetam : AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)) :=
    (measurable_const.indicator hVmeas).aestronglyMeasurable
  have hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2 := by
    filter_upwards with x
    by_cases hx : x ∈ adaptedCellAtCenter (respGrid jStar F) s w
    · simp only [heta, Set.indicator_of_mem hx, norm_one]
      norm_num
    · simp only [heta, Set.indicator_of_notMem hx, norm_zero]
      norm_num
  have hmeas := measurable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e
    uP hmax (eta := eta) hetam hetab
  have hVpos : 0 < (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq s w
  set c : ℝ := (volume (respCell jStar F t)).toReal /
    (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal with hc
  have hkey : (fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
      = fun a : CoeffSpace d => c * volumeAverage (respCell jStar F t)
          (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) := by
    funext a
    rw [volumeAverage_indicator_mul hVmeas hVU (ne_of_gt hVpos)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))]
    have hUpos : 0 < (volume (respCell jStar F t)).toReal := by
      simpa only [respCell] using adaptedCell_volume_toReal_pos (respGrid jStar F) hq t
    rw [hc]
    field_simp
  rw [hkey]
  exact hmeas.const_mul c

end

end Homogenization.HighContrast.Multiscale
