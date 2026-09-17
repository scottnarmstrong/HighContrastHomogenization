import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportXi

/-!
# The weight-field hypotheses of the duality bound, from the cutoff class

For a cutoff `φ` in the response cutoff class `IsResponseCutoff` and a matrix `qq`, put
`ξ = scalarCutoffGradientField (fun z => φ (matVecMul qq z))`.  The negative-Besov duality bound
(`e.response.cutoff.estimate`) needs three facts about this weight field: it is smooth
coordinatewise, each coordinate field has derivative bounded by the second-order scale `3^{-2t}`,
and `ξ` itself is bounded by the first-order scale `3^{-t}`, both bounds carrying only the
dimensional prefactors recorded in the cutoff class.  The declarations below discharge those three
hypotheses directly from membership in `IsResponseCutoff`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A cutoff in the response class has a coordinatewise smooth gradient field
(`e.response.cutoff.estimate`). -/
theorem contDiff_xi_of_isResponseCutoff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec d => scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y i) :=
  contDiff_scalarCutoffGradientField_comp qq h.2.2.2.2.2.1 i

/-- For a cutoff in the response class, the derivative of each coordinate of the gradient field of
the pulled-back cutoff is bounded by the second-order scale recorded in the class
(`e.response.cutoff.estimate`). -/
theorem norm_fderiv_xi_le_of_isResponseCutoff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (i : Fin d) (z : Vec d) :
    ‖fderiv ℝ
        (fun y : Vec d => scalarCutoffGradientField (fun w : Vec d => φ (matVecMul qq w)) y i)
        z‖ ≤ 1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t) :=
  norm_fderiv_scalarCutoffGradientField_comp_le qq h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 i z

/-- For a cutoff in the response class, the gradient field of the pulled-back cutoff is bounded by
the first-order scale recorded in the class (`e.response.cutoff.estimate`). -/
theorem norm_xi_le_of_isResponseCutoff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (y : Vec d) :
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖ ≤
      32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) := by
  have hΘ : (0 : ℝ) < responseCutoffProfileConst := responseCutoffProfileConst_pos
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-t) := zpow_pos (by norm_num) (-t)
  have hd : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hr : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) hΘ.le) h3.le
  calc
    ‖scalarCutoffGradientField (fun z : Vec d => φ (matVecMul qq z)) y‖
        ≤ (Real.toNNReal
            (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) : ℝ) :=
          norm_scalarCutoffGradientField_comp_le qq h.2.2.2.2.2.1 h.2.2.2.2.1 y
    _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) :=
          Real.coe_toNNReal _ hr

end

end Homogenization.HighContrast.Multiscale
