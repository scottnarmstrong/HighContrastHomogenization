import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPairing

/-!
# The cutoff cell averages of a cell and of a coarser cell containing it

The descendant telescoping of `p.response.transfer` needs, at the passage from generation `t - m`
to generation `t - m - 1`, the increment of the cutoff cell averages over a subcell `W` of the
generation-`(t - m)` aligned cell.  Because the cutoff class `IsResponseCutoff qq t φ` carries
derivatives at the scale `3^t`, `φ` varies over the cell by at most `32 d² Θ 3^{-m}`; the two
averages of `φ` over `W` and over the cell therefore differ by at most that oscillation.  This is
the weight that makes the descendant sum converge with the printed weights `3^{3(k-s)/2}`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff cell average of a subcell differs from that of the cell by the cutoff
oscillation.**  If `V` is the aligned adapted cell of generation `t - m` at the index `v` and
`W ⊆ V` has positive finite volume, the cutoff cell averages of `φ - 1` over `W` and over `V`
differ by at most `32 d² Θ 3^{-m}`.  This is the weight of the generation-`(t-m-1)` term of the
descendant sum of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_sub_volumeAverage_sub_one_le {d : ℕ} {qq : Mat d}
    (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (m : ℕ)
    (v : Fin d → ℤ) {W : Set (Vec d)}
    (hsub : W ⊆ adaptedCellAtCenter qq (t - (m : ℤ)) v)
    (hvol : (volume (adaptedCellAtCenter qq (t - (m : ℤ)) v)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (m : ℤ)) v) ≠ ⊤)
    (hint : IntegrableOn φ (adaptedCellAtCenter qq (t - (m : ℤ)) v))
    (hWvol : (volume W).toReal ≠ 0) (hWfin : volume W ≠ ⊤)
    (hWint : IntegrableOn φ W) :
    |volumeAverage W (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter qq (t - (m : ℤ)) v) (fun x => φ x - 1)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(m : ℝ)) := by
  set V : Set (Vec d) := adaptedCellAtCenter qq (t - (m : ℤ)) v with hV
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(m : ℝ)) with hK
  have : IsFiniteMeasure (volumeMeasureOn W) := by
    rw [volumeMeasureOn]
    exact isFiniteMeasure_restrict.mpr hWfin
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    rw [volumeMeasureOn, hV]
    exact isFiniteMeasure_restrict.mpr hfin
  have hvolV : (volume V).toReal ≠ 0 := by rw [hV]; exact hvol
  have hintV : IntegrableOn φ V := by rw [hV]; exact hint
  have h1W : IntegrableOn (fun _ : Vec d => (1 : ℝ)) W := integrable_const 1
  have h1V : IntegrableOn (fun _ : Vec d => (1 : ℝ)) V := integrable_const 1
  have hWpos : 0 < (volume W).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hWvol)
  have hWsub : volumeAverage W (fun x => φ x - 1) = volumeAverage W φ - 1 := by
    rw [show (fun x : Vec d => φ x - 1) = φ - fun _ => (1 : ℝ) by funext x; simp]
    rw [volumeAverage_sub hWint h1W, volumeAverage_const hWvol]
  have hVsub : volumeAverage V (fun x => φ x - 1) = volumeAverage V φ - 1 := by
    rw [show (fun x : Vec d => φ x - 1) = φ - fun _ => (1 : ℝ) by funext x; simp]
    rw [volumeAverage_sub hintV h1V, volumeAverage_const hvolV]
  have hWc : volumeAverage W (fun x => φ x - volumeAverage V φ)
      = volumeAverage W φ - volumeAverage V φ := by
    rw [show (fun x : Vec d => φ x - volumeAverage V φ)
        = φ - fun _ => volumeAverage V φ by funext x; simp]
    rw [volumeAverage_sub hWint (integrable_const (volumeAverage V φ)), volumeAverage_const hWvol]
  have hdiff : volumeAverage W (fun x => φ x - 1) - volumeAverage V (fun x => φ x - 1)
      = volumeAverage W (fun x => φ x - volumeAverage V φ) := by
    rw [hWsub, hVsub, hWc]
    ring
  have hbound : ∀ x ∈ W, |φ x - volumeAverage V φ| ≤ K := by
    intro x hx
    have hxV : x ∈ adaptedCellAtCenter qq (t - (m : ℤ)) v := hsub hx
    have h := abs_sub_volumeAverage_le_of_isResponseCutoff hq hφ m v hvol hfin hint hxV
    rw [hK, hV]
    exact h
  have hInt : |∫ x in W, (φ x - volumeAverage V φ) ∂volume| ≤ K * (volume W).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := W) (f := fun x => φ x - volumeAverage V φ) (C := K)
      (lt_top_iff_ne_top.mpr hWfin) (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hbound x hx)
    simpa only [Real.norm_eq_abs, MeasureTheory.measureReal_def] using h
  calc
    |volumeAverage W (fun x => φ x - 1) - volumeAverage V (fun x => φ x - 1)|
        = |volumeAverage W (fun x => φ x - volumeAverage V φ)| := by rw [hdiff]
    _ = |(volume W).toReal⁻¹ * ∫ x in W, (φ x - volumeAverage V φ) ∂volume| := by
          rw [volumeAverage]
    _ = (volume W).toReal⁻¹ * |∫ x in W, (φ x - volumeAverage V φ) ∂volume| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hWpos)]
    _ ≤ (volume W).toReal⁻¹ * (K * (volume W).toReal) :=
          mul_le_mul_of_nonneg_left hInt (inv_pos.mpr hWpos).le
    _ = K := by
          rw [mul_comm K (volume W).toReal, ← mul_assoc, inv_mul_cancel₀ hWvol, one_mul]

end

end Homogenization.HighContrast.Multiscale
