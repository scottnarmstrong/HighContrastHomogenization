import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPairing

/-!
# The cutoff cell decomposition against a signed integrand

The cutoff-mean rows of `p.response.transfer` pair the cutoff fluctuation with the crossed
pairing `⟨Y₂, ∇v⟩ + ⟨Y₁, a∇v⟩` of the optimizer state with the annealed mean, which has no sign.
The exact partition identity still writes the `(φ - 1)`-weighted average of a density `f` as the
normalized sum of the products of the cell means of `φ - 1` and of `f`, and on each depth-`n`
descendant cell the cutoff deviates from its own cell mean by at most
`32 d² responseCutoffProfileConst 3^{-n}`.  Because the integrand is signed, the cellwise
oscillation bound is applied against the cell average of `|f|`, so the remainder is controlled by
the terminal cell average of the absolute integrand rather than by the average of `f` itself.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- On a single descendant cell, the average of `(φ - 1) f` minus the product of the cell means
of `φ - 1` and `f` is the cell average of `(φ - (φ)_V) f`.  This is the exact per-cell identity
behind the scale gain of the cutoff estimate of `p.response.transfer`, and it requires no sign
hypothesis on the integrand. -/
private theorem volumeAverage_mul_sub_mul_volumeAverage_eq_signed
    {d : ℕ} {qq : Mat d} (t : ℤ) (n : ℕ) (w : Fin d → ℤ) {φ f : Vec d → ℝ}
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hfat : IntegrableOn f (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφfat : IntegrableOn (fun x => (φ x - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (φ x - 1) * f x)
      - (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1))
        * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) f
      = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * f x) := by
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
      (fun x => (mw - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w) := hfat.const_mul _
  have hsubeq : volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (mw - 1) * f x)
      = (mw - 1) * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) f :=
    volumeAverage_smul _ (mw - 1) f
  have hfun : ((fun x : Vec d => (φ x - 1) * f x) - fun x => (mw - 1) * f x)
      = fun x => (φ x - mw) * f x := by
    funext x
    change (φ x - 1) * f x - (mw - 1) * f x = (φ x - mw) * f x
    ring
  rw [hc, ← hsubeq, ← volumeAverage_sub hφfat hconst, hfun]

/-- On a single descendant cell, the cell average of `(φ - (φ)_V) f` is bounded by
`32 d² responseCutoffProfileConst 3^{-n}` times the cell average of `|f|`.  The oscillation of the
cutoff is paired with the absolute integrand, so no sign hypothesis on `f` is needed. -/
private theorem abs_volumeAverage_sub_cellAverage_mul_le_abs
    {d : ℕ} {qq : Mat d} (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ) {f : Vec d → ℝ}
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hfat : IntegrableOn f (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (habsat : IntegrableOn (fun x => |f x|) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφfat : IntegrableOn (fun x => (φ x - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    |volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * f x)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => |f x|) := by
  set Vw : Set (Vec d) := adaptedCellAtCenter qq (t - (n : ℤ)) w with hVw
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) with hK
  set mw : ℝ := volumeAverage Vw φ with hmw
  have hVmeas : MeasurableSet Vw :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have : IsFiniteMeasure (volumeMeasureOn Vw) := by
    rw [volumeMeasureOn, hVw]
    exact isFiniteMeasure_restrict.mpr hfin
  have hgint : IntegrableOn (fun x => (φ x - mw) * f x) Vw := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (hφfat.sub (hfat.const_mul (mw - 1))) ?_ hVmeas
    intro x _
    change (φ x - 1) * f x - (mw - 1) * f x = (φ x - mw) * f x
    ring
  have hKint : IntegrableOn (fun x => K * |f x|) Vw := habsat.const_mul K
  have hbound : ∀ x ∈ Vw, |φ x - mw| ≤ K := by
    intro x hx
    have h := abs_sub_volumeAverage_le_of_isResponseCutoff hq hφ n w hvol hfin hφat hx
    have hmw' : mw = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ := by rw [hmw, hVw]
    rw [hmw', hK]
    exact h
  have hpt : ∀ x ∈ Vw, |(φ x - mw) * f x| ≤ K * |f x| := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg (f x))
  calc |volumeAverage Vw (fun x => (φ x - mw) * f x)|
      ≤ volumeAverage Vw (fun x => K * |f x|) :=
        volumeAverage_abs_le_of_le hVmeas hpt hgint hKint
    _ = K * volumeAverage Vw (fun x => |f x|) :=
        volumeAverage_smul Vw K (fun x => |f x|)

/-- **The cutoff cell decomposition against a signed integrand.**  Replacing the cutoff by its
cell averages on the depth-`n` triadic subdivision of the terminal cell costs at most the cutoff
oscillation `32 d² Θ 3^{-n}` times the terminal cell average of the absolute integrand.  This is
the cell decomposition of the cutoff-mean rows of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_mul_sub_avsum_le_abs {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    {f : Vec d → ℝ}
    (habsint : IntegrableOn (fun x => |f x|) (HighContrast.adaptedCell qq t))
    (hφfint : IntegrableOn (fun x => (φ x - 1) * f x) (HighContrast.adaptedCell qq t))
    (hfat : ∀ w ∈ triadicIndexBox d n, IntegrableOn f (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (habsat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => |f x|) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφfat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * f x) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hvol : ∀ w ∈ triadicIndexBox d n,
      (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : ∀ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤) :
    |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * f x)
        - ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) f|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by
  let V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter qq (t - (n : ℤ)) w
  let c : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) (fun x => φ x - 1)
  let fbar : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) f
  let fabsw : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) (fun x => |f x|)
  let K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
  let g : Vec d → ℝ := fun x => (φ x - 1) * f x
  change |volumeAverage (HighContrast.adaptedCell qq t) g
      - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * fbar w|
    ≤ K * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|)
  have hpartg : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, volumeAverage (V w) g
      = volumeAverage (HighContrast.adaptedCell qq t) g :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := g) hφfint
  have hpartabs : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, fabsw w
      = volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := fun x => |f x|) habsint
  have hcell : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (V w) g - c w * fbar w
        = volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x) := by
    intro w hw
    exact volumeAverage_mul_sub_mul_volumeAverage_eq_signed t n w (hvol w hw) (hfin w hw)
      (hfat w hw) (hφat w hw) (hφfat w hw)
  have hboundw : ∀ w ∈ triadicIndexBox d n,
      |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| ≤ K * fabsw w := by
    intro w hw
    exact abs_volumeAverage_sub_cellAverage_mul_le_abs (d := d) (qq := qq) hq hφ n w
      (hvol w hw) (hfin w hw) (hfat w hw) (habsat w hw) (hφat w hw) (hφfat w hw)
  have hsumcell : (∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) g - c w * fbar w))
      = ∑ w ∈ triadicIndexBox d n,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x) :=
    Finset.sum_congr rfl (fun w hw => hcell w hw)
  have hsumabs : |∑ w ∈ triadicIndexBox d n,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)|
      ≤ ∑ w ∈ triadicIndexBox d n, K * fabsw w := by
    calc |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)|
        ≤ ∑ w ∈ triadicIndexBox d n,
            |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ triadicIndexBox d n, K * fabsw w :=
          Finset.sum_le_sum (fun w hw => hboundw w hw)
  calc |volumeAverage (HighContrast.adaptedCell qq t) g
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * fbar w|
      = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          (∑ w ∈ triadicIndexBox d n, volumeAverage (V w) g
            - ∑ w ∈ triadicIndexBox d n, c w * fbar w)| := by
            rw [← hpartg, ← mul_sub]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) g - c w * fbar w)| := by
            rw [← Finset.sum_sub_distrib]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| := by
            rw [hsumcell]
      _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * f x)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, K * fabsw w :=
            mul_le_mul_of_nonneg_left hsumabs (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = K * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, fabsw w) := by
            rw [← Finset.mul_sum (triadicIndexBox d n) fabsw K]
            ring
      _ = K * volumeAverage (HighContrast.adaptedCell qq t) (fun x => |f x|) := by rw [hpartabs]

end

end Homogenization.HighContrast.Multiscale
