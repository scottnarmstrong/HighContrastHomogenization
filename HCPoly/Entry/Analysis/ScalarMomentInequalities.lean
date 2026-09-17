import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Scalar moment inequalities for the PositiveGap support layer

This file records scalar `MemLp` consequences that do not depend on the
operator-valued Schatten infrastructure.
-/

namespace Homogenization.HighContrast.Analysis

open MeasureTheory

noncomputable section

private theorem scalar_holderConjugate_power {N : ℝ} (hN : 1 < N) :
    (N / (N - 1)).HolderConjugate N := by
  have hp : 1 < N / (N - 1) := by
    have hden : 0 < N - 1 := by linarith
    rw [lt_div_iff₀ hden]
    linarith
  rw [Real.holderConjugate_iff_eq_conjExponent hp]
  have hdenne : N - 1 ≠ 0 := by linarith
  field_simp [hdenne]
  ring

private theorem scalar_power_memLp_conjugate {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 1 < N) {f : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf : MemLp f (ENNReal.ofReal N) μ) :
    MemLp (fun x => f x ^ (N - 1)) (ENNReal.ofReal (N / (N - 1))) μ := by
  have hqpos : 0 < N - 1 := by linarith
  have hbase :
      MemLp (fun x => ‖f x‖ ^ (N - 1)) (ENNReal.ofReal (N / (N - 1))) μ := by
    convert hf.norm_rpow_div (ENNReal.ofReal (N - 1)) using 1
    · ext x
      rw [ENNReal.toReal_ofReal hqpos.le]
    · rw [ENNReal.ofReal_div_of_pos hqpos]
  exact (memLp_congr_ae (by
    filter_upwards [hf_nonneg] with x hx
    rw [Real.norm_of_nonneg hx])).mp hbase

theorem scalar_holder_power_integrable_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 1 < N) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : MemLp f (ENNReal.ofReal N) μ) (hg : MemLp g (ENNReal.ofReal N) μ) :
    Integrable (fun x => f x ^ (N - 1) * g x) μ ∧
      ∫ x, f x ^ (N - 1) * g x ∂μ ≤
        (∫ x, (f x ^ (N - 1)) ^ (N / (N - 1)) ∂μ) ^ (1 / (N / (N - 1))) *
          (∫ x, g x ^ N ∂μ) ^ (1 / N) := by
  have hpq : (N / (N - 1)).HolderConjugate N := scalar_holderConjugate_power hN
  have hfpow := scalar_power_memLp_conjugate hN hf_nonneg hf
  have : ENNReal.HolderTriple (ENNReal.ofReal (N / (N - 1))) (ENNReal.ofReal N) 1 :=
    hpq.ennrealOfReal
  have hint : Integrable (fun x => f x ^ (N - 1) * g x) μ := hfpow.integrable_mul hg
  refine ⟨hint, ?_⟩
  have hfpow_nonneg : 0 ≤ᵐ[μ] fun x => f x ^ (N - 1) := by
    filter_upwards [hf_nonneg] with x hx
    exact Real.rpow_nonneg hx _
  exact integral_mul_le_Lp_mul_Lq_of_nonneg hpq hfpow_nonneg hg_nonneg hfpow hg

theorem scalar_minkowski_toReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {N : ℝ} (hN : 1 ≤ N) {f g : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal N) μ) (hg : MemLp g (ENNReal.ofReal N) μ) :
    MemLp (fun x => f x + g x) (ENNReal.ofReal N) μ ∧
      (eLpNorm (fun x => f x + g x) (ENNReal.ofReal N) μ).toReal ≤
        (eLpNorm f (ENNReal.ofReal N) μ).toReal +
          (eLpNorm g (ENNReal.ofReal N) μ).toReal := by
  have hp1 : 1 ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hN
  have hmem : MemLp (fun x => f x + g x) (ENNReal.ofReal N) μ := by
    simpa only [Pi.add_apply] using! hf.add hg
  refine ⟨hmem, ?_⟩
  have hle :
      eLpNorm (fun x => f x + g x) (ENNReal.ofReal N) μ ≤
        eLpNorm f (ENNReal.ofReal N) μ + eLpNorm g (ENNReal.ofReal N) μ := by
    simpa only [Pi.add_apply] using!
      eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp1
  have htop :
      eLpNorm f (ENNReal.ofReal N) μ + eLpNorm g (ENNReal.ofReal N) μ ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono htop hle


/-- Identify the real scalar norm with the rooted moment on its natural nonnegative domain. -/
theorem scalar_eLpNorm_toReal_eq_root {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 0 < N) {f : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf : MemLp f (ENNReal.ofReal N) μ) :
    (eLpNorm f (ENNReal.ofReal N) μ).toReal = (∫ x, f x ^ N ∂μ) ^ N⁻¹ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hN)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hN.le]
  have heq : (∫ x, ‖f x‖ ^ N ∂μ) = ∫ x, f x ^ N ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf_nonneg] with x hx
    rw [Real.norm_of_nonneg hx]
  rw [heq, ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg_of_ae
    (hf_nonneg.mono (fun x hx => Real.rpow_nonneg hx _))) _)]

/-- The rooted mixed-moment Hölder estimate used in the positive-gap proof. -/
theorem scalar_mixedMoment_root_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 1 < N) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : MemLp f (ENNReal.ofReal N) μ) (hg : MemLp g (ENNReal.ofReal N) μ) :
    (∫ x, f x ^ (N - 1) * g x ∂μ) ^ N⁻¹ ≤
      (eLpNorm f (ENNReal.ofReal N) μ).toReal ^ (1 - N⁻¹) *
        (eLpNorm g (ENNReal.ofReal N) μ).toReal ^ N⁻¹ := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hNm : N - 1 ≠ 0 := (sub_pos.mpr hN).ne'
  have hflat : (∫ x, (f x ^ (N - 1)) ^ (N / (N - 1)) ∂μ) = ∫ x, f x ^ N ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf_nonneg] with x hx
    rw [← Real.rpow_mul hx]
    congr 1
    field_simp
  have hfp : 0 ≤ ∫ x, f x ^ N ∂μ :=
    integral_nonneg_of_ae (hf_nonneg.mono (fun x hx => Real.rpow_nonneg hx _))
  have hgp : 0 ≤ ∫ x, g x ^ N ∂μ :=
    integral_nonneg_of_ae (hg_nonneg.mono (fun x hx => Real.rpow_nonneg hx _))
  have hm : 0 ≤ ∫ x, f x ^ (N - 1) * g x ∂μ :=
    integral_nonneg_of_ae (by
      filter_upwards [hf_nonneg, hg_nonneg] with x hx hy
      exact mul_nonneg (Real.rpow_nonneg hx _) hy)
  have hh := (scalar_holder_power_integrable_bound hN hf_nonneg hg_nonneg hf hg).2
  rw [hflat] at hh
  have he : 1 / (N / (N - 1)) = N⁻¹ * (N - 1) := by field_simp
  rw [he, Real.rpow_mul hfp, one_div] at hh
  have hr := Real.rpow_le_rpow hm hh (inv_nonneg.mpr hNpos.le)
  rw [Real.mul_rpow (Real.rpow_nonneg (Real.rpow_nonneg hfp _) _) (Real.rpow_nonneg hgp _),
    ← Real.rpow_mul (Real.rpow_nonneg hfp _)] at hr
  have he' : (N - 1) * N⁻¹ = 1 - N⁻¹ := by field_simp
  rw [he'] at hr
  rw [scalar_eLpNorm_toReal_eq_root hNpos hf_nonneg hf,
    scalar_eLpNorm_toReal_eq_root hNpos hg_nonneg hg]
  exact hr

/-- Scalar Young inequality in the precise mixed-power form used for absorption. -/
theorem scalar_young_mixed {N x y : ℝ} (hN : 1 < N) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y ^ (1 - N⁻¹) * x ^ N⁻¹ ≤ (1 - N⁻¹) * y + N⁻¹ * x := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hNm : N - 1 ≠ 0 := (sub_pos.mpr hN).ne'
  have he : 1 - N⁻¹ = (N / (N - 1))⁻¹ := by field_simp
  rw [he]
  have hh := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg hy (N / (N - 1))⁻¹) (Real.rpow_nonneg hx N⁻¹)
    (scalar_holderConjugate_power hN)
  rw [Real.rpow_inv_rpow hy (div_ne_zero hNpos.ne' hNm),
    Real.rpow_inv_rpow hx hNpos.ne'] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Young absorption with the exact factor `N / (N - 1)`. -/
theorem scalar_young_absorb {N x y a : ℝ} (hN : 1 < N) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ a + y ^ (1 - N⁻¹) * x ^ N⁻¹) :
    x ≤ y + N / (N - 1) * a := by
  have hh := h.trans (add_le_add le_rfl (scalar_young_mixed hN hx hy))
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hcoef : 0 < 1 - N⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hN)
  have he : N / (N - 1) = (1 - N⁻¹)⁻¹ := by field_simp
  rw [he]
  apply (mul_le_mul_iff_right₀ hcoef).mp
  calc
    (1 - N⁻¹) * x ≤ (1 - N⁻¹) * y + a := by linarith only [hh]
    _ = (1 - N⁻¹) * (y + (1 - N⁻¹)⁻¹ * a) := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hcoef.ne', one_mul]


/-- Subadditivity of the exponent in the printed positive-gap interpolation. -/
theorem scalar_gap_power_add_le {N a b : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (1 - N⁻¹) ≤ a ^ (1 - N⁻¹) + b ^ (1 - N⁻¹) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  exact Real.rpow_add_le_add_rpow ha hb
    (sub_nonneg.mpr ((inv_le_one₀ hNpos).mpr hN))
    (sub_le_self _ (inv_nonneg.mpr hNpos.le))

/-- The paper's exact dimension coefficient after Young absorption; `m` is `2d`. -/
theorem scalar_gap_young_absorb {N m x y a : ℝ} (hN : 1 < N)
    (hm : 0 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ a + m ^ ((N - 1) / N ^ 2) * y ^ (1 - N⁻¹) * x ^ N⁻¹) :
    x ≤ m ^ N⁻¹ * y + N / (N - 1) * a := by
  apply scalar_young_absorb hN hx (mul_nonneg (Real.rpow_nonneg hm _) hy)
  rw [Real.mul_rpow (Real.rpow_nonneg hm _) hy, ← Real.rpow_mul hm]
  have he : N⁻¹ * (1 - N⁻¹) = (N - 1) / N ^ 2 := by field_simp
  rwa [he]

/-- The rational factor in the last line of the printed proof. -/
theorem scalar_gap_absorption_factor_le_two {N : ℝ} (hN : 2 ≤ N) :
    N / (N - 1) ≤ 2 := by
  apply (div_le_iff₀ (by linarith only [hN] : 0 < N - 1)).mpr
  linarith only [hN]

/-- The dimension simplification in the last line of the printed proof. -/
theorem scalar_gap_dimension_factor_le {N m : ℝ} (hN : 1 ≤ N) (hm : 0 ≤ m) :
    (2 * m) ^ (1 - N⁻¹) ≤ 2 * m ^ (1 - N⁻¹) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hm _)
  calc
    (2 : ℝ) ^ (1 - N⁻¹) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (sub_le_self _ (inv_nonneg.mpr (zero_le_one.trans hN)))
    _ = 2 := Real.rpow_one _

end

end Homogenization.HighContrast.Analysis
