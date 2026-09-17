import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECoeff
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECongr
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# The integrability of the terminal optimizer state on descendant cells

The descendant sum of `p.response.transfer` pairs the dual variable `Y` against the cell average,
over a descendant cell `V` of the terminal cell `U`, of the doubled state `X_u = (∇u, a_∓ ∇u)` of
the terminal optimizer `u`.  Each such pairing is a genuine integral, so every linear readout of
each state slot must be integrable on `V`.  The recentred coefficients `a_∓ = respCoeff∓ F a` are
elliptic only almost everywhere, so the integrability is read off a pointwise elliptic
representative on the terminal cell — one representative serves every descendant cell at every
depth, because every descendant cell is contained in the terminal cell — and transported back
across the almost-everywhere replacement, which changes the gradient slot not at all and the flux
slot only on a null set.
-/

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The state slots of the terminal optimizer are integrable on every descendant cell, minus
sign.**  For the recentred coefficient `a_- = a - g` of `p.response.transfer`, every linear readout
of the gradient slot and of the flux slot of the doubled state of the terminal optimizer is
integrable on each depth-`m` aligned descendant cell of the terminal cell. -/
theorem integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    (∀ r : Vec d, IntegrableOn
        (fun x => vecDot r (optimizerField (respCoeffMinus F a) u x).1)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
      ∧ (∀ p : Vec d, IntegrableOn
        (fun x => vecDot p (optimizerField (respCoeffMinus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (respCell jStar F t) := by
    show IsOpen (HighContrast.adaptedCell (respGrid jStar F) t)
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ respCell jStar F t := by
    show V ⊆ HighContrast.adaptedCell (respGrid jStar F) t
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_restrict.mpr (by
      rw [hVdef]
      simpa only [adaptedCellAtCenter] using
        Geometry.volume_adaptedCellTranslate_ne_top (respGrid jStar F) (t - (m : ℤ))
          (adaptedCellCenter (respGrid jStar F) (t - (m : ℤ)) W))
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u' : AHarmonicFunction f V :=
    (aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hVopen hVU hEllV with hu'
  have hgrad : u'.toH1.grad = u.toH1.grad := by
    rw [hu']
    simp only [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn, H1Function.restrict]
    exact grad_aHarmonicFunctionOfAEEqCoeff hae u
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  constructor
  · intro r
    simpa only [optimizerField, hgrad] using hdata.grad r u'
  · intro p
    have hcongr : (fun x => vecDot p (matVecMul (f x) (u'.toH1.grad x)))
        =ᵐ[volumeMeasureOn V]
          (fun x => vecDot p (matVecMul ((respCoeffMinus F a) x) (u.toH1.grad x))) := by
      filter_upwards [haeV.symm] with x hx
      rw [hx, hgrad]
    simpa only [optimizerField] using (hdata.flux p u').congr_fun_ae hcongr

/-- **The state slots of the terminal optimizer are integrable on every descendant cell, plus
sign.**  The adjoint twin, for the recentred coefficient `a_+ = aᵀ + g`. -/
theorem integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    (∀ r : Vec d, IntegrableOn
        (fun x => vecDot r (optimizerField (respCoeffPlus F a) u x).1)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
      ∧ (∀ p : Vec d, IntegrableOn
        (fun x => vecDot p (optimizerField (respCoeffPlus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (respCell jStar F t) := by
    show IsOpen (HighContrast.adaptedCell (respGrid jStar F) t)
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ respCell jStar F t := by
    show V ⊆ HighContrast.adaptedCell (respGrid jStar F) t
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_restrict.mpr (by
      rw [hVdef]
      simpa only [adaptedCellAtCenter] using
        Geometry.volume_adaptedCellTranslate_ne_top (respGrid jStar F) (t - (m : ℤ))
          (adaptedCellCenter (respGrid jStar F) (t - (m : ℤ)) W))
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u' : AHarmonicFunction f V :=
    (aHarmonicFunctionOfAEEqCoeff hae u).restrictOfIsEllipticFieldOn hU hVopen hVU hEllV with hu'
  have hgrad : u'.toH1.grad = u.toH1.grad := by
    rw [hu']
    simp only [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn, H1Function.restrict]
    exact grad_aHarmonicFunctionOfAEEqCoeff hae u
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  constructor
  · intro r
    simpa only [optimizerField, hgrad] using hdata.grad r u'
  · intro p
    have hcongr : (fun x => vecDot p (matVecMul (f x) (u'.toH1.grad x)))
        =ᵐ[volumeMeasureOn V]
          (fun x => vecDot p (matVecMul ((respCoeffPlus F a) x) (u.toH1.grad x))) := by
      filter_upwards [haeV.symm] with x hx
      rw [hx, hgrad]
    simpa only [optimizerField] using (hdata.flux p u').congr_fun_ae hcongr

/-- **The crossed pairing of the terminal optimizer state is integrable on every descendant cell,
minus sign.**  The scalar crossed pairing `⟨Y₂, ∇u⟩ + ⟨Y₁, a_-∇u⟩` of the descendant sum of
`p.response.transfer`, and its modulus, are integrable on each depth-`m` aligned descendant cell. -/
theorem integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    IntegrableOn (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      ∧ IntegrableOn (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2|)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) := by
  obtain ⟨hgrad, hflux⟩ :=
    integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t m a u hW
  constructor
  · simpa [MeasureTheory.IntegrableOn] using! (hgrad Y.2).integrable.add (hflux Y.1).integrable
  · simpa [MeasureTheory.IntegrableOn, Pi.add_apply] using
      ((hgrad Y.2).integrable.add (hflux Y.1).integrable).abs

/-- **The crossed pairing of the terminal optimizer state is integrable on every descendant cell,
plus sign.**  The adjoint twin, for the recentred coefficient `a_+ = aᵀ + g` and the dual variable
`Y^+`. -/
theorem integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    IntegrableOn (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      ∧ IntegrableOn (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2|)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) := by
  obtain ⟨hgrad, hflux⟩ :=
    integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t m a u hW
  constructor
  · simpa [MeasureTheory.IntegrableOn] using! (hgrad Y.2).integrable.add (hflux Y.1).integrable
  · simpa [MeasureTheory.IntegrableOn, Pi.add_apply] using
      ((hgrad Y.2).integrable.add (hflux Y.1).integrable).abs

end

end Homogenization.HighContrast.Multiscale
