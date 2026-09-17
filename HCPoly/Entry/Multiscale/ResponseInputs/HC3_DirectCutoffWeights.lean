import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCutoffOsc
import HCPoly.Entry.Geometry.AdaptedCellTransport
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The subcell means of the cutoff fluctuation

In the terminal-optimizer replacement of `p.response.transfer` the cutoff fluctuation `φ - 1` is
replaced, on each aligned subcell of the coarse scale, by its mean there.  Those means are the
weights of the row.  This module records the two elementary analytic facts the row assembly
consumes alongside the already-recorded mean-zero identity: the cutoff and its fluctuation are
integrable on every aligned adapted cell, and each subcell mean of the fluctuation is at most one
in absolute value.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A cutoff `φ` of the response class `IsResponseCutoff qq t φ` is integrable on every aligned
adapted cell `adaptedCellAtCenter qq j w`.  The class makes `φ` continuous with compact support, so `φ`
is integrable on the whole space and hence on any set.  This is the integrability of the cutoff on
the subcells of the row assembly of `p.response.transfer`. -/
theorem integrableOn_isResponseCutoff {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq) {t : ℤ}
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (j : ℤ) (w : Fin d → ℤ) :
    MeasureTheory.IntegrableOn φ (adaptedCellAtCenter qq j w) := by
  have hcont : Continuous φ := hφ.contDiff.continuous
  have hint : Integrable φ := hcont.integrable_of_hasCompactSupport hφ.hasCompactSupport
  have hVopen : IsOpen (adaptedCellAtCenter qq j w) :=
    Geometry.isOpen_adaptedCellTranslate hq j _
  exact hint.integrableOn.congr_fun (fun x _ => rfl) hVopen.measurableSet

/-- The cutoff fluctuation `φ - 1` of the response class `IsResponseCutoff qq t φ` is integrable on
every aligned adapted cell `adaptedCellAtCenter qq j w`.  The cutoff is integrable there and so is the
constant `1`, because the aligned cell has finite volume.  This is the integrability of the subcell
weights of the centred cutoff decomposition of `p.response.transfer`. -/
theorem integrableOn_sub_one_isResponseCutoff {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq)
    {t : ℤ} {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (j : ℤ) (w : Fin d → ℤ) :
    MeasureTheory.IntegrableOn (fun x => φ x - 1) (adaptedCellAtCenter qq j w) := by
  have hVfin : volume (adaptedCellAtCenter qq j w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top qq j w
  exact (integrableOn_isResponseCutoff hq hφ j w).sub (integrableOn_const hVfin)

/-- Every subcell mean of the cutoff fluctuation `φ - 1` is at most one in absolute value.  The
response class confines `φ` to `[0, 2]`, so the fluctuation `φ - 1` lies in `[-1, 1]`; its volume
average over an aligned adapted cell therefore inherits the bound, because the cell has finite
nonzero volume.  These are the weights of the row assembly of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_isResponseCutoff_le_one {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (j : ℤ)
    (w : Fin d → ℤ) :
    |volumeAverage (adaptedCellAtCenter qq j w) (fun x => φ x - 1)| ≤ 1 := by
  have hVfin : volume (adaptedCellAtCenter qq j w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top qq j w
  have hVpos : 0 < (volume (adaptedCellAtCenter qq j w)).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ j)]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det qq).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ j) d)
  have hbound : |∫ x in adaptedCellAtCenter qq j w, (φ x - 1) ∂volume|
      ≤ (volume (adaptedCellAtCenter qq j w)).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := adaptedCellAtCenter qq j w) (f := fun x => φ x - 1) (C := 1)
      (lt_top_iff_ne_top.mpr hVfin) (fun x _ => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by have h0 := hφ.nonneg x; linarith,
          by have h2 := hφ.le_two x; linarith⟩)
    rw [Real.norm_eq_abs, one_mul, MeasureTheory.measureReal_def] at h
    exact h
  unfold volumeAverage
  rw [abs_mul, abs_of_pos (inv_pos.mpr hVpos)]
  calc (volume (adaptedCellAtCenter qq j w)).toReal⁻¹
        * |∫ x in adaptedCellAtCenter qq j w, (φ x - 1) ∂volume|
      ≤ (volume (adaptedCellAtCenter qq j w)).toReal⁻¹ * (volume (adaptedCellAtCenter qq j w)).toReal :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hVpos)

end

end Homogenization.HighContrast.Multiscale
