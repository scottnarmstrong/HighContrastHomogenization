import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCutoffOsc
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage

/-!
# The cutoff fluctuation splits into cell means plus a `3^{-n}` remainder

The scale gain of the cutoff estimate of `p.response.transfer`.  Exact partition averaging over the
generation-`(t - n)` triadic subdivision writes the `(φ - 1)`-weighted average of a density `D` as
the normalized average of the per-cell weighted averages of `φ - 1` and `D`.  On each descendant
cell `V`, replacing `φ - 1` by its own `V`-mean costs only the oscillation of `φ` on `V`, which is
at most `32 d² responseCutoffProfileConst 3^{-n}`.  Summing back gives the stated remainder bound;
the remaining cell-mean term is the one cancelled in expectation by stationarity.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Across a descendant adapted cell `adaptedCellAtCenter qq (t - n) w`, a cutoff `φ` of the response
class `IsResponseCutoff qq t φ` deviates from its cell mean by at most
`32 d² responseCutoffProfileConst 3^{-n}`.  This is the oscillation input to the scale gain of the
cutoff estimate of `p.response.transfer`. -/
theorem abs_sub_volumeAverage_le_of_isResponseCutoff {d : ℕ} {qq : Mat d} (hq : IsUnit qq)
    {t : ℤ} {φ : Vec d → ℝ} (h : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ)
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hint : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    {x : Vec d} (hx : x ∈ adaptedCellAtCenter qq (t - (n : ℤ)) w) :
    |φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by
  set V : Set (Vec d) := adaptedCellAtCenter qq (t - (n : ℤ)) w with hV
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) with hK
  have hVmeas : MeasurableSet V :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hvolV : (volume V).toReal ≠ 0 := by rw [hV]; exact hvol
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    rw [volumeMeasureOn, hV]
    exact isFiniteMeasure_restrict.mpr hfin
  have hupper : volumeAverage V φ ≤ φ x + K := by
    refine volumeAverage_le_of_le_on hVmeas hint hvolV ?_
    intro y hy
    have hb := abs_sub_le_of_mem_adaptedCellAtCenter hq h n w hy hx
    have h2 : φ y - φ x ≤ K := (abs_le.mp hb).2
    linarith
  have hlower : φ x - K ≤ volumeAverage V φ := by
    have hle : ∀ y ∈ V, φ x - K ≤ φ y := by
      intro y hy
      have hb := abs_sub_le_of_mem_adaptedCellAtCenter hq h n w hy hx
      have h1 : -K ≤ φ y - φ x := (abs_le.mp hb).1
      linarith
    have hcomp := volumeAverage_le_volumeAverage_of_le_on hVmeas
      (integrable_const (φ x - K)) hint hle
    rwa [volumeAverage_const hvolV] at hcomp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- On a single descendant cell, the average of `(φ - 1) D` minus the product of the cell means of
`φ - 1` and `D` is the cell average of `(φ - (φ)_V) D`.  This is the exact per-cell identity
behind the scale gain of `p.response.transfer`. -/
private theorem volumeAverage_mul_sub_mul_volumeAverage_eq
    {d : ℕ} {qq : Mat d} (t : ℤ) (n : ℕ) (w : Fin d → ℤ) {φ D : Vec d → ℝ}
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hDat : IntegrableOn D (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφDat : IntegrableOn (fun x => (φ x - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (φ x - 1) * D x)
      - (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1))
        * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D
      = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * D x) := by
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter qq (t - (n : ℤ)) w)) := by
    rw [volumeMeasureOn]
    exact isFiniteMeasure_restrict.mpr hfin
  set mw : ℝ := volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ with hmw
  have h1 : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (adaptedCellAtCenter qq (t - (n : ℤ)) w) :=
    integrable_const 1
  have hc : volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1) = mw - 1 := by
    rw [show (fun x : Vec d => φ x - 1) = φ - fun _ => (1 : ℝ) by funext x; simp]
    rw [volumeAverage_sub hφat h1, volumeAverage_const hvol, ← hmw]
  have hconst : IntegrableOn
      (fun x => (mw - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w) := hDat.const_mul _
  have hsubeq : volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (mw - 1) * D x)
      = (mw - 1) * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D :=
    volumeAverage_smul _ (mw - 1) D
  have hfun : ((fun x : Vec d => (φ x - 1) * D x) - fun x => (mw - 1) * D x)
      = fun x => (φ x - mw) * D x := by
    funext x
    change (φ x - 1) * D x - (mw - 1) * D x = (φ x - mw) * D x
    ring
  rw [hc, ← hsubeq, ← volumeAverage_sub hφDat hconst, hfun]

/-- On a single descendant cell, the cell average of `(φ - (φ)_V) D` is bounded by
`32 d² responseCutoffProfileConst 3^{-n}` times the cell average of `D`, using the oscillation of
`φ` on the cell and the nonnegativity of `D`. -/
private theorem abs_volumeAverage_sub_cellAverage_mul_le
    {d : ℕ} {qq : Mat d} (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ) {D : Vec d → ℝ}
    (hD : ∀ x, 0 ≤ D x)
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hDat : IntegrableOn D (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφDat : IntegrableOn (fun x => (φ x - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    |volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * D x)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D := by
  set Vw : Set (Vec d) := adaptedCellAtCenter qq (t - (n : ℤ)) w with hVw
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) with hK
  set mw : ℝ := volumeAverage Vw φ with hmw
  have hVmeas : MeasurableSet Vw :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have : IsFiniteMeasure (volumeMeasureOn Vw) := by
    rw [volumeMeasureOn, hVw]
    exact isFiniteMeasure_restrict.mpr hfin
  have hvolV : (volume Vw).toReal ≠ 0 := by rw [hVw]; exact hvol
  have hgint : IntegrableOn (fun x => (φ x - mw) * D x) Vw := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (hφDat.sub (hDat.const_mul (mw - 1))) ?_ hVmeas
    intro x _
    change (φ x - 1) * D x - (mw - 1) * D x = (φ x - mw) * D x
    ring
  have hKint : IntegrableOn (fun x => K * D x) Vw := hDat.const_mul K
  have hnKint : IntegrableOn (fun x => -K * D x) Vw := hDat.const_mul (-K)
  have hbound : ∀ x ∈ Vw, |φ x - mw| ≤ K := by
    intro x hx
    have h := abs_sub_volumeAverage_le_of_isResponseCutoff hq hφ n w hvol hfin hφat hx
    have hmw' : mw = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ := by rw [hmw, hVw]
    rw [hmw', hK]
    exact h
  have hup : ∀ x ∈ Vw, (φ x - mw) * D x ≤ K * D x := by
    intro x hx
    exact mul_le_mul_of_nonneg_right (abs_le.mp (hbound x hx)).2 (hD x)
  have hlo : ∀ x ∈ Vw, -K * D x ≤ (φ x - mw) * D x := by
    intro x hx
    exact mul_le_mul_of_nonneg_right (abs_le.mp (hbound x hx)).1 (hD x)
  have hUb : volumeAverage Vw (fun x => (φ x - mw) * D x)
      ≤ volumeAverage Vw (fun x => K * D x) :=
    volumeAverage_le_volumeAverage_of_le_on hVmeas hgint hKint hup
  have hLb : volumeAverage Vw (fun x => -K * D x)
      ≤ volumeAverage Vw (fun x => (φ x - mw) * D x) :=
    volumeAverage_le_volumeAverage_of_le_on hVmeas hnKint hgint hlo
  have hKavg : volumeAverage Vw (fun x => K * D x) = K * volumeAverage Vw D :=
    volumeAverage_smul Vw K D
  have hnKavg : volumeAverage Vw (fun x => -K * D x) = -(K * volumeAverage Vw D) := by
    rw [show (fun x : Vec d => -K * D x) = (-K) • D by funext x; simp]
    rw [volumeAverage_smul, neg_mul]
  rw [hKavg] at hUb
  rw [hnKavg] at hLb
  exact abs_le.mpr ⟨hLb, hUb⟩

/-- The exact partition average of the `(φ - 1)`-weighted density over the adapted parent cell
differs from the normalized sum of the products of the per-cell means of `φ - 1` and of `D` by at
most `32 d² responseCutoffProfileConst 3^{-n}` times the parent average of `D`.  This is the scale
gain of the cutoff estimate of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_mul_sub_avsum_le {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    {D : Vec d → ℝ} (hD : ∀ x, 0 ≤ D x)
    (hDint : IntegrableOn D (HighContrast.adaptedCell qq t))
    (hφDint : IntegrableOn (fun x => (φ x - 1) * D x) (HighContrast.adaptedCell qq t))
    (hDat : ∀ w ∈ triadicIndexBox d n, IntegrableOn D (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφDat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hvol : ∀ w ∈ triadicIndexBox d n,
      (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : ∀ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤) :
    |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * D x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) D := by
  let V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter qq (t - (n : ℤ)) w
  let c : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) (fun x => φ x - 1)
  let dbar : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) D
  let K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
  let f : Vec d → ℝ := fun x => (φ x - 1) * D x
  change |volumeAverage (HighContrast.adaptedCell qq t) f
      - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * dbar w|
    ≤ K * volumeAverage (HighContrast.adaptedCell qq t) D
  have hpartf : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, volumeAverage (V w) f
      = volumeAverage (HighContrast.adaptedCell qq t) f :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := f) hφDint
  have hpartD : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, dbar w = volumeAverage (HighContrast.adaptedCell qq t) D :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := D) hDint
  have hcell : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (V w) f - c w * dbar w
        = volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x) := by
    intro w hw
    exact volumeAverage_mul_sub_mul_volumeAverage_eq t n w (hvol w hw) (hfin w hw)
      (hDat w hw) (hφat w hw) (hφDat w hw)
  have hboundw : ∀ w ∈ triadicIndexBox d n,
      |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| ≤ K * dbar w := by
    intro w hw
    exact abs_volumeAverage_sub_cellAverage_mul_le (d := d) (qq := qq) hq hφ n w hD
      (hvol w hw) (hfin w hw) (hDat w hw) (hφat w hw) (hφDat w hw)
  have hsumcell : (∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) f - c w * dbar w))
      = ∑ w ∈ triadicIndexBox d n,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x) :=
    Finset.sum_congr rfl (fun w hw => hcell w hw)
  have hsumabs : |∑ w ∈ triadicIndexBox d n,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)|
      ≤ ∑ w ∈ triadicIndexBox d n, K * dbar w := by
    calc |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)|
        ≤ ∑ w ∈ triadicIndexBox d n,
            |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ triadicIndexBox d n, K * dbar w :=
          Finset.sum_le_sum (fun w hw => hboundw w hw)
  calc |volumeAverage (HighContrast.adaptedCell qq t) f
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * dbar w|
      = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          (∑ w ∈ triadicIndexBox d n, volumeAverage (V w) f
            - ∑ w ∈ triadicIndexBox d n, c w * dbar w)| := by
            rw [← hpartf, ← mul_sub]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) f - c w * dbar w)| := by
            rw [← Finset.sum_sub_distrib]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| := by
            rw [hsumcell]
      _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, K * dbar w :=
            mul_le_mul_of_nonneg_left hsumabs (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = K * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, dbar w) := by
            rw [← Finset.mul_sum (triadicIndexBox d n) dbar K]
            ring
      _ = K * volumeAverage (HighContrast.adaptedCell qq t) D := by rw [hpartD]

end

end Homogenization.HighContrast.Multiscale
