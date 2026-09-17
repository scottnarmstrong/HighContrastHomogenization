import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscCell
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsBlockPSD
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECongr
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# The crossed pairing of the terminal optimizer on a descendant cell, at the carriers

Each generation increment of the descendant sum of `p.response.transfer` pairs the dual variable
`Y` with the cell average, over a descendant cell of the terminal cell, of the doubled state
`(∇u, a∇u)` of the terminal optimizer `u`.  The Fenchel probe bounds each of the two crossed slots
by the two-term head of that cell times the square root of twice the half cell energy, so their sum
is bounded by the head times the square root of twice the doubled cell energy.  The probe is stated
for a pointwise elliptic coefficient, while the recentred coefficients `a_∓` are elliptic only
almost everywhere; it is therefore run at a pointwise elliptic representative on the terminal cell,
which serves every descendant cell at once, and every quantity is transported back across the
almost-everywhere replacement.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The square root of twice the doubled energy is twice the square root of twice the half energy;
no sign hypothesis is needed, because the square root of a negative number is zero on both
sides. -/
private theorem sqrt_two_mul_two_mul (X : ℝ) :
    Real.sqrt (2 * (2 * X)) = 2 * Real.sqrt (2 * ((1 / 2 : ℝ) * X)) := by
  have h1 : (2 : ℝ) * (2 * X) = 4 * X := by ring
  have h2 : (2 : ℝ) * ((1 / 2 : ℝ) * X) = X := by ring
  rw [h1, h2, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) X,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]

/-- **The crossed pairing of the terminal optimizer on a descendant cell, minus sign.**  On each
depth-`m` aligned descendant cell of the terminal cell, the cell average of the scalar crossed
pairing `⟨Y₂, ∇u⟩ + ⟨Y₁, a_-∇u⟩` of the terminal optimizer is at most the pathwise two-term head of
that cell times the square root of twice the doubled cell energy.  This is the pathwise input of
the descendant sum of `p.response.transfer`. -/
theorem abs_volumeAverage_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter_le
    {d : ℕ} [NeZero d] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m)
    (hX1 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hX2 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY1 : IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY2 : IntegrableOn
      (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) :
    |volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffMinus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffMinus F a)).lowerRight Y.2)))
        * Real.sqrt (2 * (2 * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) u))) := by
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
  have hvol : 0 < (volume V).toReal := by
    rw [hVdef]
    exact volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq (t - (m : ℤ)) W
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
  -- the two slots of the state, at the representative and at the recentred coefficient
  have hfst : ∀ x, (optimizerField f u₀ x).1
      = (optimizerField (respCoeffMinus F a) u x).1 := by
    intro x
    simp only [optimizerField, hgrad]
  have hsnd : (fun x => (optimizerField f u₀ x).2)
      =ᵐ[volumeMeasureOn V] fun x => (optimizerField (respCoeffMinus F a) u x).2 := by
    filter_upwards [haeV.symm] with x hx
    simp only [optimizerField, hgrad, hx]
  have hX1' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).1 i) V := by
    intro i
    refine (hX1 i).congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)
    exact congrFun (hfst x).symm i
  have hX2' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).2 i) V := by
    intro i
    refine (hX2 i).congr_fun_ae ?_
    filter_upwards [hsnd] with x hx
    exact congrFun hx.symm i
  have hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V f).upperLeft Y.1) :=
    zero_le_vecDot_coarseBlockMatrix_upperLeft hConv hEllV hvol Y.1
  have hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V f).lowerRight Y.2) :=
    zero_le_vecDot_coarseBlockMatrix_lowerRight hConv hEllV hvol Y.2
  obtain ⟨hg, hf⟩ := abs_volumeAverage_cross_le_head_mul_sqrt hU hVopen hVU hConv hEllV hvol u₀ Y
    hA1 hA2 hX1' hX2'
  -- transport of the coarse block and of the cell energy
  have hC : coarseBlockMatrix V f = coarseBlockMatrix V (respCoeffMinus F a) :=
    (coarseBlockMatrix_congr_of_ae_eq haeV).symm
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  -- transport of the two slot averages
  have hgA : volumeAverage V (fun x => vecDot Y.2 (optimizerField f u₀ x).1)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1) := by
    refine congrArg (volumeAverage V) ?_
    funext x
    rw [hfst x]
  have hfA : volumeAverage V (fun x => vecDot Y.1 (optimizerField f u₀ x).2)
      = volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [hsnd] with x hx
    rw [hx]
  rw [hgA] at hg
  rw [hfA] at hf
  rw [hC, hE] at hg hf
  -- split the average of the sum and collect
  set G : ℝ :=
    Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V (respCoeffMinus F a)).upperLeft Y.1))
      + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V (respCoeffMinus F a)).lowerRight Y.2))
    with hGdef
  set X : ℝ := volumeAverage V (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) with hXdef
  have hsplit : volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
        + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2) := by
    have h := volumeAverage_add (U := V) hY1 hY2
    simpa only [Pi.add_apply] using! h
  rw [hsplit, sqrt_two_mul_two_mul X]
  calc |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)|
      ≤ |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1)|
        + |volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)| :=
        abs_add_le _ _
    _ ≤ G * Real.sqrt (2 * ((1 / 2 : ℝ) * X))
        + G * Real.sqrt (2 * ((1 / 2 : ℝ) * X)) := add_le_add hg hf
    _ = G * (2 * Real.sqrt (2 * ((1 / 2 : ℝ) * X))) := by ring

/-- **The crossed pairing of the terminal optimizer on a descendant cell, plus sign.**  The adjoint
twin of `abs_volumeAverage_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter_le`, for the recentred
coefficient `a_+ = aᵀ + g` and the dual variable `Y^+`. -/
theorem abs_volumeAverage_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter_le
    {d : ℕ} [NeZero d] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m)
    (hX1 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) u x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hX2 : ∀ i : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) u x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY1 : IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
    (hY2 : IntegrableOn
      (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) :
    |volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffPlus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffPlus F a)).lowerRight Y.2)))
        * Real.sqrt (2 * (2 * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) u))) := by
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
  have hvol : 0 < (volume V).toReal := by
    rw [hVdef]
    exact volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq (t - (m : ℤ)) W
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
  have hfst : ∀ x, (optimizerField f u₀ x).1
      = (optimizerField (respCoeffPlus F a) u x).1 := by
    intro x
    simp only [optimizerField, hgrad]
  have hsnd : (fun x => (optimizerField f u₀ x).2)
      =ᵐ[volumeMeasureOn V] fun x => (optimizerField (respCoeffPlus F a) u x).2 := by
    filter_upwards [haeV.symm] with x hx
    simp only [optimizerField, hgrad, hx]
  have hX1' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).1 i) V := by
    intro i
    refine (hX1 i).congr_fun_ae (Filter.Eventually.of_forall fun x => ?_)
    exact congrFun (hfst x).symm i
  have hX2' : ∀ i : Fin d, IntegrableOn (fun x => (optimizerField f u₀ x).2 i) V := by
    intro i
    refine (hX2 i).congr_fun_ae ?_
    filter_upwards [hsnd] with x hx
    exact congrFun hx.symm i
  have hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V f).upperLeft Y.1) :=
    zero_le_vecDot_coarseBlockMatrix_upperLeft hConv hEllV hvol Y.1
  have hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V f).lowerRight Y.2) :=
    zero_le_vecDot_coarseBlockMatrix_lowerRight hConv hEllV hvol Y.2
  obtain ⟨hg, hf⟩ := abs_volumeAverage_cross_le_head_mul_sqrt hU hVopen hVU hConv hEllV hvol u₀ Y
    hA1 hA2 hX1' hX2'
  have hC : coarseBlockMatrix V f = coarseBlockMatrix V (respCoeffPlus F a) :=
    (coarseBlockMatrix_congr_of_ae_eq haeV).symm
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  have hgA : volumeAverage V (fun x => vecDot Y.2 (optimizerField f u₀ x).1)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1) := by
    refine congrArg (volumeAverage V) ?_
    funext x
    rw [hfst x]
  have hfA : volumeAverage V (fun x => vecDot Y.1 (optimizerField f u₀ x).2)
      = volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [hsnd] with x hx
    rw [hx]
  rw [hgA] at hg
  rw [hfA] at hf
  rw [hC, hE] at hg hf
  set G : ℝ :=
    Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V (respCoeffPlus F a)).upperLeft Y.1))
      + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V (respCoeffPlus F a)).lowerRight Y.2))
    with hGdef
  set X : ℝ := volumeAverage V (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) with hXdef
  have hsplit : volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
        + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)
      = volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2) := by
    have h := volumeAverage_add (U := V) hY1 hY2
    simpa only [Pi.add_apply] using! h
  rw [hsplit, sqrt_two_mul_two_mul X]
  calc |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)
        + volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)|
      ≤ |volumeAverage V (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1)|
        + |volumeAverage V (fun x => vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)| :=
        abs_add_le _ _
    _ ≤ G * Real.sqrt (2 * ((1 / 2 : ℝ) * X))
        + G * Real.sqrt (2 * ((1 / 2 : ℝ) * X)) := add_le_add hg hf
    _ = G * (2 * Real.sqrt (2 * ((1 / 2 : ℝ) * X))) := by ring

end

end Homogenization.HighContrast.Multiscale
