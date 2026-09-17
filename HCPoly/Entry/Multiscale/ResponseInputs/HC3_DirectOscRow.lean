import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffEnergyDefect

/-!
# The cutoff oscillation against the terminal-optimizer energy

In the terminal-optimizer replacement of `p.response.transfer`, the cutoff fluctuation `φ - 1` is
split on each aligned subcell of the coarse scale into its subcell mean and its oscillation there.
The oscillation part costs the Lipschitz gain `3^{-H}` of the cutoff class times the energy of the
terminal optimizer, which at a maximizer is twice the pathwise response.  This module records that
step for the optimizer's energy density, replacing the general nonnegative density of the
oscillation split by the concrete one the estimate uses.

Paper: `p.response.transfer`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff oscillation of the terminal-optimizer energy.**  On the adapted cell `⋄_t^q`, for
a cutoff `φ` of the response class and a response maximizer `u` of the loads `(p, r)`, the
`(φ − 1)`-weighted optimizer energy differs from the normalized sum of the products of the subcell
means of `φ − 1` and of the energy by at most the oscillation cost
`32 d² responseCutoffProfileConst 3^{-n}` times twice the pathwise response `J(⋄_t^q; p, r; b)`.
The variation energy of the terminal optimizer is nonnegative only on the cell, so the oscillation
split is applied to its positive part, which agrees with it there, and at a maximizer the
cell-average energy is exactly `2 J`.  This is the scale-gain step of the cutoff estimate of
`p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_energy_sub_avsum_le {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hmax : IsResponseMaximizer (HighContrast.adaptedCell q t) p r b u)
    (hu_int : weakFluxIntegrable (HighContrast.adaptedCell q t) b u)
    (hresp_u : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) (HighContrast.adaptedCell q t))
    (hlin_self : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand (HighContrast.adaptedCell q t) b p r u u)
      (HighContrast.adaptedCell q t))
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand b u)
      (HighContrast.adaptedCell q t))
    (hφE : MeasureTheory.IntegrableOn
      (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x) (HighContrast.adaptedCell q t))
    (hEat : ∀ w ∈ triadicIndexBox d n, MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand b u) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hφat : ∀ w ∈ triadicIndexBox d n, MeasureTheory.IntegrableOn φ
      (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hφEat : ∀ w ∈ triadicIndexBox d n, MeasureTheory.IntegrableOn
      (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x)
      (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    |volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand b u)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
          (2 * respJ q t p r b) := by
  set Dpos : Vec d → ℝ := fun x => max (scalarVariationEnergyIntegrand b u x) 0 with hDposdef
  have hUmeas : MeasurableSet (HighContrast.adaptedCell q t) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen.measurableSet
  have hVmeas : ∀ w : Fin d → ℤ,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hsub : ∀ w ∈ triadicIndexBox d n,
      adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hDpos_nonneg : ∀ x, 0 ≤ Dpos x := by
    intro x
    rw [hDposdef]
    exact le_max_right _ _
  have hDpos_eq_on : ∀ x ∈ HighContrast.adaptedCell q t,
      Dpos x = scalarVariationEnergyIntegrand b u x := by
    intro x hx
    rw [hDposdef]
    exact max_eq_left
      (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (HighContrast.adaptedCell q t) b hEll u x hx)
  have hDpos_U : IntegrableOn Dpos (HighContrast.adaptedCell q t) :=
    henergy.congr_fun (fun x hx => (hDpos_eq_on x hx).symm) hUmeas
  have hφDpos_U : IntegrableOn (fun x => (φ x - 1) * Dpos x) (HighContrast.adaptedCell q t) :=
    hφE.congr_fun (fun x hx => by rw [hDpos_eq_on x hx]) hUmeas
  have hDpos_at : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn Dpos (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    intro w hw
    exact (hEat w hw).congr_fun
      (fun x hx => (hDpos_eq_on x (hsub w hw hx)).symm) (hVmeas w)
  have hφDpos_at : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * Dpos x) (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    intro w hw
    exact (hφEat w hw).congr_fun
      (fun x hx => by rw [hDpos_eq_on x (hsub w hw hx)]) (hVmeas w)
  have hvolAt : ∀ w : Fin d → ℤ,
      0 < (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal := by
    intro w
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det q).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - (n : ℤ))) d)
  have hsplit := abs_volumeAverage_sub_one_mul_sub_avsum_le (d := d) (qq := q) hq t n hφ
    (D := Dpos) hDpos_nonneg hDpos_U hφDpos_U hDpos_at hφat hφDpos_at
    (fun w _ => ne_of_gt (hvolAt w))
    (fun w _ => Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w)
  have havgU_f : volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * Dpos x)
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x) := by
    unfold volumeAverage
    rw [MeasureTheory.setIntegral_congr_fun hUmeas (fun x hx => by rw [hDpos_eq_on x hx])]
  have havgU_D : volumeAverage (HighContrast.adaptedCell q t) Dpos
      = volumeAverage (HighContrast.adaptedCell q t)
          (scalarVariationEnergyIntegrand b u) := by
    unfold volumeAverage
    rw [MeasureTheory.setIntegral_congr_fun hUmeas (fun x hx => hDpos_eq_on x hx)]
  have havgV_D : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Dpos
        = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand b u) := by
    intro w hw
    unfold volumeAverage
    rw [MeasureTheory.setIntegral_congr_fun (hVmeas w)
      (fun x hx => hDpos_eq_on x (hsub w hw hx))]
  have hterms : (∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => φ x - 1)
          * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Dpos)
      = ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => φ x - 1)
          * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarVariationEnergyIntegrand b u) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [havgV_D w hw]
  have henergy_avg : volumeAverage (HighContrast.adaptedCell q t)
        (scalarVariationEnergyIntegrand b u) = 2 * respJ q t p r b := by
    have h := responseJ_energy_of_isResponseMaximizer (HighContrast.adaptedCell q t) b p r u
      hmax hu_int hresp_u hlin_self henergy
    unfold respJ
    linarith
  rw [havgU_f, hterms, havgU_D] at hsplit
  rw [henergy_avg] at hsplit
  exact hsplit

end

end Homogenization.HighContrast.Multiscale
