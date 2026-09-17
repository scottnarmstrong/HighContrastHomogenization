import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsObligations

/-!
# The two named error rows are monotone in their constant

The energy-defect row and the cutoff-mean row of `p.response.transfer` are produced with different
constants — `max 3 (32 d² Θ)` and `max 1 (respCutoffOscConst d)` — while the row assembly consumes
both at one common constant.  Both right-hand sides are the constant times a nonnegative quantity,
so raising the constant preserves the bound.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The energy-defect row weakens as the constant grows. -/
theorem cutoffEnergyDefectRowMinus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hτ : 0 ≤ respTauMinus P jStar F s t e) (hEJ : 0 ≤ respEJMinus P jStar F t e)
    (hCC : C ≤ C') (h : CutoffEnergyDefectRowMinus C P jStar F H s t e φ uM) :
    CutoffEnergyDefectRowMinus C' P jStar F H s t e φ uM := by
  unfold CutoffEnergyDefectRowMinus at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_right hCC ?_)
  have h1 : (0 : ℝ) ≤ Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) :=
    Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e :=
    mul_nonneg (by positivity) hEJ
  linarith

/-- The adjoint energy-defect row weakens as the constant grows. -/
theorem cutoffEnergyDefectRowPlus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hτ : 0 ≤ respTauPlus P jStar F s t e) (hEJ : 0 ≤ respEJPlus P jStar F t e)
    (hCC : C ≤ C') (h : CutoffEnergyDefectRowPlus C P jStar F H s t e φ uP) :
    CutoffEnergyDefectRowPlus C' P jStar F H s t e φ uP := by
  unfold CutoffEnergyDefectRowPlus at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_right hCC ?_)
  have h1 : (0 : ℝ) ≤ Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
    Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e :=
    mul_nonneg (by positivity) hEJ
  linarith

/-- The cutoff-mean row weakens as the constant grows. -/
theorem cutoffMeanRowMinus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hCC : C ≤ C') (h : CutoffMeanRowMinus C P jStar F H s t e φ uM) :
    CutoffMeanRowMinus C' P jStar F H s t e φ uM := by
  unfold CutoffMeanRowMinus at h ⊢
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right hCC ?_))
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- The adjoint cutoff-mean row weakens as the constant grows. -/
theorem cutoffMeanRowPlus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hCC : C ≤ C') (h : CutoffMeanRowPlus C P jStar F H s t e φ uP) :
    CutoffMeanRowPlus C' P jStar F H s t e φ uP := by
  unfold CutoffMeanRowPlus at h ⊢
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right hCC ?_))
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

end

end Homogenization.HighContrast.Multiscale
