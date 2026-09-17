import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH612

/-!
# The weak-norm estimate, assembled over the two signs

`response_weak_estimate_of_route` is `e.response.weak.estimate`: the supremum over families of
response maximizers of the per-family weak energy is bounded by
`(C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2})^2` for each sign.  It is obtained from the two
per-family bounds by taking the larger of the two constants and reading the supremum off
through the two conjuncts of the definition of `W^±`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **`e.response.weak.estimate`.**  For each sign, `W^± ≥ 0` and
`(W^±)^{1/2} ≤ C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2}`.

`W^±` is a supremum over all families of response maximizers, so the bound follows from the
per-family bounds `respWeakEnergyOf_minus_le` and `respWeakEnergyOf_plus_le` once the two
constants are replaced by their maxima; the supremum is then bounded because every member of
the defining set is. -/
theorem response_weak_estimate_of_route (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (Cc Ce Cl Cm Cs : ℝ) (hCc : 0 < Cc)
    (hCe : 0 < Ce) (hCl : 0 < Cl) (hCm : 0 < Cm) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ (C : ℝ) (CH : ℕ → ℝ), 0 < C ∧ (∀ n : ℕ, 0 < CH n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
              ∀ e : Vec d, vecDot e e = 1 →
                RespEnergyDefect Ce P jStar F s t e →
                RespLoadMean Cl P jStar F s t e →
                RespWeakBound C CH d γ P jStar F H η s t e := by
  obtain ⟨Csrc₁, hCsrc₁, C₁, CH₁, hC₁, hCH₁, h₁⟩ :=
    respWeakEnergyOf_minus_le d hd γ hγ S hS Cc Ce Cl Cm Cs hCc hCe hCl hCm hCs
  obtain ⟨Csrc₂, hCsrc₂, C₂, CH₂, hC₂, hCH₂, h₂⟩ :=
    respWeakEnergyOf_plus_le d hd γ hγ S hS Cc Ce Cl Cm Cs hCc hCe hCl hCm hCs
  refine ⟨max Csrc₁ Csrc₂, lt_max_of_lt_left hCsrc₁, max C₁ C₂,
    fun n => max (CH₁ n) (CH₂ n), lt_max_of_lt_left hC₁,
    fun n => lt_max_of_lt_left (hCH₁ n), ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hraw hcal η hη hprof
    hsrc hM e he hdef hload
  have hraw₁ := h612_rawOutput_le_csrc hraw (le_max_left Csrc₁ Csrc₂)
  have hraw₂ := h612_rawOutput_le_csrc hraw (le_max_right Csrc₁ Csrc₂)
  have hR0 : 0 ≤ (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hZ0 : 0 ≤ η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))) := Real.rpow_nonneg hη.1.le _
  have hκ0 : 0 ≤ Real.sqrt (respKappa P jStar F s) := Real.sqrt_nonneg _
  set R : ℝ := (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) with hR
  set Z : ℝ := η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))) with hZ
  set κ : ℝ := Real.sqrt (respKappa P jStar F s) with hκ
  have hC : 0 < max C₁ C₂ := lt_max_of_lt_left hC₁
  have hCH : 0 < max (CH₁ H) (CH₂ H) := lt_max_of_lt_left (hCH₁ H)
  have hB0 : 0 ≤ max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ := by positivity
  have hmono₁ : (C₁ * (R + CH₁ H * Z) * κ) ^ 2 ≤
      (max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ) ^ 2 := by
    have h1 : 0 ≤ C₁ * (R + CH₁ H * Z) * κ := by
      have := (hCH₁ H).le
      positivity
    have h2 : C₁ * (R + CH₁ H * Z) * κ ≤ max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ := by
      have hCle : C₁ ≤ max C₁ C₂ := le_max_left _ _
      have hCHle : CH₁ H ≤ max (CH₁ H) (CH₂ H) := le_max_left _ _
      have hsum_nonneg : 0 ≤ R + CH₁ H * Z := add_nonneg hR0 (mul_nonneg (hCH₁ H).le hZ0)
      have hmax_nonneg : 0 ≤ max C₁ C₂ := hC₁.le.trans hCle
      have hsum_le : R + CH₁ H * Z ≤ R + max (CH₁ H) (CH₂ H) * Z := by
        have h := mul_le_mul_of_nonneg_right hCHle hZ0
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul hCle hsum_le hsum_nonneg hmax_nonneg) hκ0
    exact pow_le_pow_left₀ h1 h2 2
  have hmono₂ : (C₂ * (R + CH₂ H * Z) * κ) ^ 2 ≤
      (max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ) ^ 2 := by
    have h1 : 0 ≤ C₂ * (R + CH₂ H * Z) * κ := by
      have := (hCH₂ H).le
      positivity
    have h2 : C₂ * (R + CH₂ H * Z) * κ ≤ max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ := by
      have hCle : C₂ ≤ max C₁ C₂ := le_max_right _ _
      have hCHle : CH₂ H ≤ max (CH₁ H) (CH₂ H) := le_max_right _ _
      have hsum_nonneg : 0 ≤ R + CH₂ H * Z := add_nonneg hR0 (mul_nonneg (hCH₂ H).le hZ0)
      have hmax_nonneg : 0 ≤ max C₁ C₂ := hC₂.le.trans hCle
      have hsum_le : R + CH₂ H * Z ≤ R + max (CH₁ H) (CH₂ H) * Z := by
        have h := mul_le_mul_of_nonneg_right hCHle hZ0
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul hCle hsum_le hsum_nonneg hmax_nonneg) hκ0
    exact pow_le_pow_left₀ h1 h2 2
  unfold RespWeakBound respWMinus respWPlus
  refine ⟨respWeakEnergy_nonneg _ _ _ _ _ _ _ _, respWeakEnergy_nonneg _ _ _ _ _ _ _ _, ?_, ?_⟩
  · refine sqrt_respWeakEnergy_le _ _ _ _ _ _ _ _ _ hB0 ?_
    intro u hu
    exact (h₁ ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hraw₁ hcal η hη
      hprof hsrc hM e he hdef hload u hu).trans hmono₁
  · refine sqrt_respWeakEnergy_le _ _ _ _ _ _ _ _ _ hB0 ?_
    intro u hu
    exact (h₂ ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hraw₂ hcal η hη
      hprof hsrc hM e he hdef hload u hu).trans hmono₂

end

end Homogenization.HighContrast.Multiscale
