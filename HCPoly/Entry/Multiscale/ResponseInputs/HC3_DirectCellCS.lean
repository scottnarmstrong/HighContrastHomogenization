import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectEnergySplit

/-!
# Averaged Cauchy--Schwarz in the coefficient metric

The terminal-optimizer comparison of `p.response.transfer` pairs one gradient field against
another in the metric `symmPart a`, and controls the pairing by the two diagonal energies through
Cauchy--Schwarz for the averaged bilinear form.  This module records that averaged inequality on a
set carrying a pointwise elliptic coefficient, in the normalized-average form the estimate uses.

* `abs_volumeAverage_vecDot_symmPart_le` — averaged Cauchy--Schwarz for `symmPart a`.

Paper: `p.response.transfer`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Integral Cauchy–Schwarz for two nonnegative integrable functions:
`∫ √f·√g ≤ √(∫f)·√(∫g)`. -/
private theorem integral_sqrt_mul_sqrt_le_aux
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ x, Real.sqrt (f x) * Real.sqrt (g x) ∂μ ≤
      Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
  have hsf_meas : AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hsg_meas : AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hsqf : (fun x => Real.sqrt (f x) ^ 2) =ᵐ[μ] f := by
    filter_upwards [hf0] with x hx
    rw [Real.sq_sqrt hx]
  have hsqg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hg0] with x hx
    rw [Real.sq_sqrt hx]
  have hmemf : MemLp (fun x => Real.sqrt (f x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsf_meas).2 (hf.congr hsqf.symm)
  have hmemg : MemLp (fun x => Real.sqrt (g x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsg_meas).2 (hg.congr hsqg.symm)
  have hsf0 : 0 ≤ᵐ[μ] fun x => Real.sqrt (f x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hsg0 : 0 ≤ᵐ[μ] fun x => Real.sqrt (g x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    hsf0 hsg0 (by simpa using hmemf) (by simpa using hmemg)
  have hrf : ∫ x, Real.sqrt (f x) ^ (2 : ℝ) ∂μ = ∫ x, f x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf0] with x hx
      rw [Real.rpow_two, Real.sq_sqrt hx])
  have hrg : ∫ x, Real.sqrt (g x) ^ (2 : ℝ) ∂μ = ∫ x, g x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hg0] with x hx
      rw [Real.rpow_two, Real.sq_sqrt hx])
  rw [hrf, hrg] at key
  rw [Real.sqrt_eq_rpow (∫ x, f x ∂μ), Real.sqrt_eq_rpow (∫ x, g x ∂μ)]
  convert key using 2

/-- **Averaged Cauchy–Schwarz in the coefficient metric.**  On a set `U` carrying a coefficient
`a` elliptic pointwise, the volume average of the `symmPart a`-pairing of two vector fields is
bounded by the geometric mean of the averages of their two diagonal energies:
`|⨍_U f · symmPart a g| ≤ √(⨍_U f · symmPart a f) · √(⨍_U g · symmPart a g)`.  No hypothesis on
the measure of `U` is needed: the normalizing constant `(volume U).toReal⁻¹` is nonnegative and
factors through both sides, so the degenerate cases are covered as well. -/
theorem abs_volumeAverage_vecDot_symmPart_le {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (f g : Vec d → Vec d)
    (hff : MeasureTheory.IntegrableOn
      (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (f x))) U)
    (hgg : MeasureTheory.IntegrableOn
      (fun x => vecDot (g x) (matVecMul (symmPart (a x)) (g x))) U)
    (hfg : MeasureTheory.IntegrableOn
      (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (g x))) U) :
    |volumeAverage U (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (g x)))|
      ≤ Real.sqrt (volumeAverage U (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (f x))))
        * Real.sqrt (volumeAverage U (fun x => vecDot (g x) (matVecMul (symmPart (a x)) (g x)))) := by
  let A : Vec d → ℝ := fun x => vecDot (f x) (matVecMul (symmPart (a x)) (f x))
  let B : Vec d → ℝ := fun x => vecDot (g x) (matVecMul (symmPart (a x)) (g x))
  let H : Vec d → ℝ := fun x => vecDot (f x) (matVecMul (symmPart (a x)) (g x))
  have hA_int : IntegrableOn A U := hff
  have hB_int : IntegrableOn B U := hgg
  have hH_int : IntegrableOn H U := hfg
  have hSsymm : ∀ x, matTranspose (symmPart (a x)) = symmPart (a x) :=
    fun x => matTranspose_symmPart (a x)
  have hSpsd : ∀ x ∈ U, ∀ z : Vec d, 0 ≤ vecDot z (matVecMul (symmPart (a x)) z) := by
    intro x hx z
    have hEllx : IsEllipticMatrix lam Lam (a x) := hEll.2 x hx
    have hlow := lowerBound_symmPart_of_isEllipticMatrix hEllx z
    have hlam : 0 ≤ lam := le_of_lt hEllx.1
    have hnn : 0 ≤ vecNormSq z := vecNormSq_nonneg z
    exact le_trans (mul_nonneg hlam hnn) hlow
  have hpoint : ∀ x ∈ U, |H x| ≤ Real.sqrt (A x) * Real.sqrt (B x) := by
    intro x hx
    exact abs_vecDot_matVecMul_le_sqrt_mul_sqrt (hSsymm x) (hSpsd x hx) (f x) (g x)
  have hprod_meas : AEStronglyMeasurable
      (fun x => Real.sqrt (A x) * Real.sqrt (B x)) (volume.restrict U) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA_int.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hB_int.aestronglyMeasurable)
  have hbound : ∀ᵐ x ∂(volume.restrict U),
      ‖Real.sqrt (A x) * Real.sqrt (B x)‖ ≤ A x + B x := by
    refine (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall ?_)
    intro x hx
    have hAx : 0 ≤ A x := hSpsd x hx (f x)
    have hBx : 0 ≤ B x := hSpsd x hx (g x)
    have hAB : Real.sqrt (A x) * Real.sqrt (B x) ≤ A x + B x := by
      nlinarith [sq_nonneg (Real.sqrt (A x) - Real.sqrt (B x)),
        Real.sq_sqrt hAx, Real.sq_sqrt hBx]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith
  have hprod_int : Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x))
      (volume.restrict U) :=
    Integrable.mono' (hA_int.add hB_int) hprod_meas hbound
  have hstep_abs : |volumeAverage U H| ≤ volumeAverage U (fun x => |H x|) := by
    have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    have habs : |∫ x in U, H x| ≤ ∫ x in U, |H x| := abs_integral_le_integral_abs
    calc |volumeAverage U H|
        = (volume U).toReal⁻¹ * |∫ x in U, H x| := by
            unfold volumeAverage
            rw [abs_mul, abs_of_nonneg hc]
      _ ≤ (volume U).toReal⁻¹ * ∫ x in U, |H x| :=
            mul_le_mul_of_nonneg_left habs hc
      _ = volumeAverage U (fun x => |H x|) := by
            unfold volumeAverage
            rfl
  have hstep_mono : volumeAverage U (fun x => |H x|)
      ≤ volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x)) := by
    have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    have habsH : Integrable (fun x => |H x|) (volume.restrict U) := by
      simpa [Real.norm_eq_abs] using hH_int.abs
    unfold volumeAverage
    apply mul_le_mul_of_nonneg_left _ hc
    exact integral_mono_ae habsH hprod_int
      ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => hpoint x hx)))
  have hA_nonneg : 0 ≤ᵐ[volume.restrict U] A :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => hSpsd x hx (f x)))
  have hB_nonneg : 0 ≤ᵐ[volume.restrict U] B :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => hSpsd x hx (g x)))
  have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hcs : (∫ x in U, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in U, A x) * Real.sqrt (∫ x in U, B x) :=
    integral_sqrt_mul_sqrt_le_aux hA_int hB_int hA_nonneg hB_nonneg
  have hsqrtc : Real.sqrt ((volume U).toReal⁻¹) * Real.sqrt ((volume U).toReal⁻¹)
      = (volume U).toReal⁻¹ := Real.mul_self_sqrt hc
  have hsqrtA : Real.sqrt (volumeAverage U A)
      = Real.sqrt ((volume U).toReal⁻¹) * Real.sqrt (∫ x in U, A x) := by
    rw [show volumeAverage U A = (volume U).toReal⁻¹ * ∫ x in U, A x from rfl,
      Real.sqrt_mul hc (∫ x in U, A x)]
  have hsqrtB : Real.sqrt (volumeAverage U B)
      = Real.sqrt ((volume U).toReal⁻¹) * Real.sqrt (∫ x in U, B x) := by
    rw [show volumeAverage U B = (volume U).toReal⁻¹ * ∫ x in U, B x from rfl,
      Real.sqrt_mul hc (∫ x in U, B x)]
  have hstep_cs : volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (volumeAverage U A) * Real.sqrt (volumeAverage U B) := by
    calc volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x))
        = (volume U).toReal⁻¹ * ∫ x in U, Real.sqrt (A x) * Real.sqrt (B x) := rfl
      _ ≤ (volume U).toReal⁻¹
            * (Real.sqrt (∫ x in U, A x) * Real.sqrt (∫ x in U, B x)) :=
            mul_le_mul_of_nonneg_left hcs hc
      _ = Real.sqrt (volumeAverage U A) * Real.sqrt (volumeAverage U B) := by
            rw [hsqrtA, hsqrtB]
            conv_lhs => rw [← hsqrtc]
            ring
  calc |volumeAverage U H|
      ≤ volumeAverage U (fun x => |H x|) := hstep_abs
    _ ≤ volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x)) := hstep_mono
    _ ≤ Real.sqrt (volumeAverage U A) * Real.sqrt (volumeAverage U B) := hstep_cs

end

end Homogenization.HighContrast.Multiscale
