import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscSigned
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectExpansionInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscCarrier
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# The vanishing remainder of the descendant refinement

The oscillation half of the cutoff-mean row of `p.response.transfer` refines the terminal cell
down to the generation `t - (H + N)` and keeps the defect of the depth-`(H+N)` cell part as a
remainder.  The cell decomposition against a signed integrand bounds that defect by
`32 d² Θ 3^{-(H+N)}` times the terminal cell average of the modulus of the integrand; splitting the
power as `3^{-H} · 3^{-N}` exhibits the printed factor `3^{-H}` of the row and leaves a remainder
that vanishes geometrically in the refinement depth `N`.  The `(φ-1)`-weighted integrand is
integrable wherever the integrand is, a response cutoff taking values in `[0, 2]`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The `(φ-1)`-weighted integrand is integrable wherever the integrand is.**  A response cutoff
is smooth and takes values in `[0, 2]`, so `|φ - 1| ≤ 1` and multiplying by `φ - 1` preserves
integrability on any measurable set of finite volume. -/
theorem integrableOn_isResponseCutoff_sub_one_mul {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUfin : volume U ≠ ⊤) {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) {f : Vec d → ℝ} (hf : IntegrableOn f U) :
    IntegrableOn (fun x => (φ x - 1) * f x) U := by
  obtain ⟨hφ0, hφ2, -, -, -, hsmooth, -⟩ := hφ
  have hmeas : Measurable fun x : Vec d => φ x - 1 :=
    (hsmooth.continuous.measurable).sub measurable_const
  have hbd : ∀ x : Vec d, |φ x - 1| ≤ 1 := by
    intro x
    rw [abs_le]
    constructor <;> linarith only [hφ0 x, hφ2 x]
  exact integrableOn_cutoff_mul_coord hU hUfin hmeas hbd hf

/-- **The remainder of the descendant refinement carries the printed `3^{-H}`.**  Replacing the
cutoff by its cell means on the depth-`(H+N)` triadic subdivision of the terminal cell costs at
most `(32 d² Θ 3^{-H}) · 3^{-N}` times the terminal cell average of the modulus of the integrand.
This is the remainder of the oscillation half of `p.response.transfer`, which vanishes as the
refinement depth `N` grows. -/
theorem abs_volumeAverage_sub_one_mul_sub_avsum_shift_le {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) (t : ℤ) (H N : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    {f : Vec d → ℝ}
    (habsint : IntegrableOn (fun x => |f x|) (HighContrast.adaptedCell qq t))
    (hfint : IntegrableOn f (HighContrast.adaptedCell qq t))
    (hfat : ∀ w ∈ triadicIndexBox d (H + N),
      IntegrableOn f (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w))
    (habsat : ∀ w ∈ triadicIndexBox d (H + N),
      IntegrableOn (fun x => |f x|) (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w)) :
    |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * f x)
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) f|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by
  have hUmeas : MeasurableSet (HighContrast.adaptedCell qq t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hUfin : volume (HighContrast.adaptedCell qq t) ≠ ⊤ := by
    have h0 : HighContrast.adaptedCellTranslate qq t 0 = HighContrast.adaptedCell qq t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.volume_adaptedCellTranslate_ne_top qq t 0
  have hφfint : IntegrableOn (fun x => (φ x - 1) * f x) (HighContrast.adaptedCell qq t) :=
    integrableOn_isResponseCutoff_sub_one_mul hUmeas hUfin hφ hfint
  have hVmeas : ∀ w : Fin d → ℤ,
      MeasurableSet (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - ((H + N : ℕ) : ℤ)) w).measurableSet
  have hVfin : ∀ w : Fin d → ℤ,
      volume (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) ≠ ⊤ :=
    fun w => Geometry.volume_adaptedCellAtCenter_ne_top qq _ w
  have hVpos : ∀ w : Fin d → ℤ,
      (volume (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w)).toReal ≠ 0 :=
    fun w => ne_of_gt (volume_adaptedCellAtCenter_toReal_pos qq hq _ w)
  have hmain := abs_volumeAverage_sub_one_mul_sub_avsum_le_abs (d := d) (qq := qq) hq t (H + N)
    hφ habsint hφfint hfat habsat
    (fun w _ => integrableOn_isResponseCutoff hq hφ _ w)
    (fun w _ => integrableOn_isResponseCutoff_sub_one_mul (hVmeas w) (hVfin w) hφ (hfat w ‹_›))
    (fun w _ => hVpos w) (fun w _ => hVfin w)
  have hpow : (3 : ℝ) ^ (-(((H + N : ℕ) : ℝ))) =
      (3 : ℝ) ^ (-(H : ℝ)) * (3 : ℝ) ^ (-(N : ℝ)) := by
    rw [show -(((H + N : ℕ) : ℝ)) = -(H : ℝ) + -(N : ℝ) by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  calc |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * f x)
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - ((H + N : ℕ) : ℤ)) w) f|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(((H + N : ℕ) : ℝ)))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by
        rw [hpow]; ring

end

end Homogenization.HighContrast.Multiscale
