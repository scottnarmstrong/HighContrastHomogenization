import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectEnergyDepth
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRestrictResp
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECongr
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# The doubled descendant cell energy of the terminal optimizer at the carriers

The descendant sum of `p.response.transfer` pairs each cell head with the square root of twice the
cell energy of the terminal optimizer, and the sum of the two crossed slots carries the doubled
energy rather than the half energy.  Rescaling the annealed flat average of twice the half energy
by the constant `4` gives the doubled form, with the dual energy `E[J_t^∓]` replaced by
`4 E[J_t^∓]`.  Each cell energy is nonnegative because the symmetric part of an elliptic
coefficient is positive semidefinite; the recentred coefficients are elliptic only almost
everywhere, so this is read at a pointwise elliptic representative and transported back.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The descendant cell energy of the terminal optimizer is nonnegative, minus sign.**  On every
aligned descendant cell of the terminal cell, the cell average of the variation energy integrand of
the recentred coefficient `a_- = a - g` is nonnegative. -/
theorem zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffMinus_adaptedCellAtCenter
    {d : ℕ} [NeZero d] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ HighContrast.adaptedCell (respGrid jStar F) t := by
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hConv : IsOpenBoundedConvexDomain V := by
    rw [hVdef]
    exact isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq (t - (m : ℤ)) W
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u₀ : AHarmonicFunction f (HighContrast.adaptedCell (respGrid jStar F) t) :=
    aHarmonicFunctionOfAEEqCoeff hae u with hu₀
  have hgrad : u₀.toH1.grad = u.toH1.grad := by
    rw [hu₀]
    exact grad_aHarmonicFunctionOfAEEqCoeff hae u
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  have hnn : 0 ≤ volumeAverage V (scalarVariationEnergyIntegrand f
      (u₀.restrictOfIsEllipticFieldOn hU hVopen hVU hEllV)) :=
    volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V f hEllV _
  rw [scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hVopen hVU hEllV u₀] at hnn
  rwa [hE] at hnn

/-- **The descendant cell energy of the terminal optimizer is nonnegative, plus sign.**  The
adjoint twin, for the recentred coefficient `a_+ = aᵀ + g`. -/
theorem zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffPlus_adaptedCellAtCenter
    {d : ℕ} [NeZero d] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ HighContrast.adaptedCell (respGrid jStar F) t := by
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hConv : IsOpenBoundedConvexDomain V := by
    rw [hVdef]
    exact isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq (t - (m : ℤ)) W
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u₀ : AHarmonicFunction f (HighContrast.adaptedCell (respGrid jStar F) t) :=
    aHarmonicFunctionOfAEEqCoeff hae u with hu₀
  have hgrad : u₀.toH1.grad = u.toH1.grad := by
    rw [hu₀]
    exact grad_aHarmonicFunctionOfAEEqCoeff hae u
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  have hnn : 0 ≤ volumeAverage V (scalarVariationEnergyIntegrand f
      (u₀.restrictOfIsEllipticFieldOn hU hVopen hVU hEllV)) :=
    volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V f hEllV _
  rw [scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hVopen hVU hEllV u₀] at hnn
  rwa [hE] at hnn

/-- **The annealed flat average of the doubled descendant cell energies, minus sign.**  The
expectation of the flat average over the depth-`m` aligned cells of twice the doubled cell energy
of the terminal optimizer is `2 * (4 E[J_t^-])`, the value the descendant sum of
`p.response.transfer` consumes. -/
theorem integral_avsum_two_mul_doubledEnergy_eq_respEJMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) ∂P)
      = 2 * (4 * respEJMinus P jStar F t e) := by
  have hbase := integral_avsum_two_mul_halfEnergy_eq_respEJMinus P jStar F t m e hq uM hmax
    hEint hJ
  have hpt : ∀ a : CoeffSpace d,
      (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
        = 4 * ((((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
            2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) := by
    intro a
    have h1 : ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
        = ∑ W ∈ triadicIndexBox d m,
          4 * (2 * ((1 / 2 : ℝ) * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) :=
      Finset.sum_congr rfl (fun W _ => by ring)
    rw [h1, ← Finset.mul_sum]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hbase]
  ring

/-- **The annealed flat average of the doubled descendant cell energies, plus sign.**  The adjoint
twin, with `4 E[J_t^+]`. -/
theorem integral_avsum_two_mul_doubledEnergy_eq_respEJPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) ∂P)
      = 2 * (4 * respEJPlus P jStar F t e) := by
  have hbase := integral_avsum_two_mul_halfEnergy_eq_respEJPlus P jStar F t m e hq uP hmax
    hEint hJ
  have hpt : ∀ a : CoeffSpace d,
      (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
        = 4 * ((((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
            2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) := by
    intro a
    have h1 : ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
        = ∑ W ∈ triadicIndexBox d m,
          4 * (2 * ((1 / 2 : ℝ) * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) :=
      Finset.sum_congr rfl (fun W _ => by ring)
    rw [h1, ← Finset.mul_sum]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hbase]
  ring

end

end Homogenization.HighContrast.Multiscale
