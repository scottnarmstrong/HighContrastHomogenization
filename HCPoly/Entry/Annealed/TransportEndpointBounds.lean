import HCPoly.Entry.Annealed.TransportDriftComparison
namespace Homogenization.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- The length premise supplies the missing positive length and the final decay. -/
theorem transport_length_decay (C ρ : ℝ) (hC : 1 ≤ C) (hρ : ρ ∈ Set.Ioc (0 : ℝ) 1)
    (L : ℕ) (hL : C + Real.logb 3 ρ⁻¹ ≤ (L : ℝ)) :
    1 ≤ L ∧ (3 : ℝ) ^ (-(L : ℝ)) ≤ ρ := by
  have hlog : 0 ≤ Real.logb 3 ρ⁻¹ := Real.logb_nonneg (by norm_num) ((one_le_inv₀ hρ.1).2 hρ.2)
  have hLreal : (1 : ℝ) ≤ L := by linarith only [hC, hL, hlog]
  refine ⟨by exact_mod_cast hLreal, ?_⟩
  calc
    _ ≤ (3 : ℝ) ^ (-Real.logb 3 ρ⁻¹) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith only [hC, hL])
    _ = ρ := by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr hρ.1), inv_inv]

/-- Nonnegativity permits weighting the two terms of the smallness premise. -/
theorem transport_weighted_smallness (γ p D ρ L : ℝ) (hγ : γ < 1) (hL : 0 ≤ L)
    (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hsmall : p + D ≤ (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * L) * ρ) :
    (3 : ℝ) ^ ((1 - γ) / 2 * L) * p + (3 : ℝ) ^ ((1 - γ) / 4 * L) * D ≤ ρ ∧
    (3 : ℝ) ^ ((1 - γ) / 2 * L) * p ≤ ρ ∧
    (3 : ℝ) ^ ((1 - γ) / 4 * L) * D ≤ ρ := by
  have hw : (3 : ℝ) ^ ((1 - γ) / 4 * L) ≤ (3 : ℝ) ^ ((1 - γ) / 2 * L) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [mul_nonneg (sub_pos.mpr hγ).le hL])
  have hh := mul_le_mul_of_nonneg_left hsmall
    (by positivity : 0 ≤ (3 : ℝ) ^ ((1 - γ) / 2 * L))
  have he : (3 : ℝ) ^ ((1 - γ) / 2 * L) * (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * L) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    convert Real.rpow_zero (3 : ℝ) using 1
    congr 1
    ring
  rw [← mul_assoc, he, one_mul, mul_add] at hh
  have hcomb := (add_le_add le_rfl (mul_le_mul_of_nonneg_right hw hD)).trans hh
  exact ⟨hcomb, (le_add_of_nonneg_right (mul_nonneg (by positivity) hD)).trans hcomb,
    (le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hcomb⟩

/-- A linear factor is uniformly bounded by a positive exponential. -/
theorem transport_linear_rpow_bound (b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    (1 + 2 * x) * (3 : ℝ) ^ (-b * x) ≤ 1 + 2 / (b * Real.log 3) := by
  let c := b * Real.log 3
  have hc : 0 < c := mul_pos hb (Real.log_pos (by norm_num))
  have hexp : 1 ≤ Real.exp (c * x) := Real.one_le_exp_iff.mpr (mul_nonneg hc.le hx)
  have hlin : c * x ≤ Real.exp (c * x) := by linarith only [Real.add_one_le_exp (c * x)]
  have hlin' : x ≤ Real.exp (c * x) / c := (le_div_iff₀ hc).2 (by linarith only [hlin])
  have hbound : 1 + 2 * x ≤ (1 + 2 / c) * Real.exp (c * x) := by
    calc
      _ ≤ Real.exp (c * x) + 2 * (Real.exp (c * x) / c) := by linarith only [hexp, hlin']
      _ = _ := by ring
  have he : (3 : ℝ) ^ (-b * x) = Real.exp (-(c * x)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp only [c]
    ring
  rw [he]
  calc
    _ ≤ ((1 + 2 / c) * Real.exp (c * x)) * Real.exp (-(c * x)) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Ordered source constants absorb both printed source terms, including the linear scale factor. -/
theorem exists_transport_source_absorption (a Q : ℝ) (ha : 0 < a) (hQ : 0 ≤ Q) :
    ∃ Csep Cpoly : ℝ, 1 ≤ Csep ∧ 0 < Cpoly ∧
      ∀ A L x : ℝ, 1 ≤ A → 0 ≤ L →
        Csep * (L + Real.logb 3 A) ≤ x →
        A ^ Q * (3 : ℝ) ^ (-(2 * a) * x) ≤ (3 : ℝ) ^ (-L) ∧
        A * (1 + x + L) * (3 : ℝ) ^ (-a * x) ≤ Cpoly * (3 : ℝ) ^ (-L) := by
  let Csep := max 1 (max ((Q + 1) / (2 * a)) (4 / a))
  let Cpoly := 1 + 2 / ((a / 2) * Real.log 3)
  have hC1 : 1 ≤ Csep := le_max_left _ _
  have hCQ : (Q + 1) / (2 * a) ≤ Csep := (le_max_left _ _).trans (le_max_right _ _)
  have hCa : 4 / a ≤ Csep := (le_max_right _ _).trans (le_max_right _ _)
  have hCQ' : Q + 1 ≤ 2 * a * Csep := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * a)).mp hCQ
    linarith only [this]
  have hCa' : 4 ≤ a * Csep := by have := (div_le_iff₀ ha).mp hCa; linarith only [this]
  refine ⟨Csep, Cpoly, hC1, by dsimp only [Cpoly]; positivity, ?_⟩
  intro A L x hA hL hsep
  let y := Real.logb 3 A
  have hy : 0 ≤ y := Real.logb_nonneg (by norm_num) hA
  have hxy : L + y ≤ x := (le_mul_of_one_le_left (add_nonneg hL hy) hC1).trans hsep
  have hx : 0 ≤ x := (add_nonneg hL hy).trans hxy
  have heQ : A ^ Q = (3 : ℝ) ^ (Q * y) := by
    rw [mul_comm Q y, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) (zero_lt_one.trans_le hA)]
  have hexp : Q * y - 2 * a * x ≤ -L := by
    have h1 := mul_le_mul_of_nonneg_left hsep (show 0 ≤ 2 * a by positivity)
    have h2 := mul_le_mul_of_nonneg_right hCQ' (add_nonneg hL hy)
    change 2 * a * (Csep * (L + y)) ≤ 2 * a * x at h1
    nlinarith only [h1, h2, mul_nonneg hQ hL, hy]
  have hquarter : L + y ≤ a / 4 * x := by
    have h1 := mul_le_mul_of_nonneg_left hsep ha.le
    have h2 := mul_le_mul_of_nonneg_right hCa' (add_nonneg hL hy)
    nlinarith only [h1, h2]
  refine ⟨?_, ?_⟩
  · rw [heQ, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith only [hexp]
  · have hAexp : A * (3 : ℝ) ^ (-(a / 4) * x) ≤ 1 := by
      conv_lhs => lhs; rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1) (zero_lt_one.trans_le hA)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by dsimp only [y] at hquarter; linarith only [hquarter, hL])
    have hdecay : (3 : ℝ) ^ (-(a / 4) * x) ≤ (3 : ℝ) ^ (-L) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hquarter, hy])
    have hpoly : (1 + x + L) * (3 : ℝ) ^ (-(a / 2) * x) ≤ Cpoly := by
      apply le_trans _ (transport_linear_rpow_bound (a / 2) x (by positivity) hx)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith only [hxy, hy]
    have hnonneg : 0 ≤ (1 + x + L) * (3 : ℝ) ^ (-(a / 2) * x) := by positivity
    calc
      _ = (A * (3 : ℝ) ^ (-(a / 4) * x)) *
          ((1 + x + L) * (3 : ℝ) ^ (-(a / 2) * x)) * (3 : ℝ) ^ (-(a / 4) * x) := by
        have he : (3 : ℝ) ^ (-a * x) = (3 : ℝ) ^ (-(a / 4) * x) *
            (3 : ℝ) ^ (-(a / 2) * x) * (3 : ℝ) ^ (-(a / 4) * x) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          congr 1
          ring
        rw [he]
        ring
      _ ≤ 1 * Cpoly * (3 : ℝ) ^ (-L) := mul_le_mul
        (mul_le_mul hAexp hpoly hnonneg (by norm_num)) hdecay (by positivity) (by dsimp only [Cpoly]; positivity)
      _ = _ := by rw [one_mul]

/-- Projective proximity bounds the two distinct source brackets by one geometric base. -/
theorem transport_source_brackets (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ Pi e ePlus : ℝ, 1 ≤ Pi → 1 ≤ e → 0 ≤ ePlus →
      ePlus ≤ Real.exp 1 * e →
      1 + Pi * (K₀ * e * ePlus + ePlus ^ 2) ≤ B * ((2 + Pi) * e ^ 2) ∧
      1 + Pi * (e + ePlus) ^ 2 ≤ B * ((2 + Pi) * e ^ 2) := by
  let c := Real.exp 1
  let b₁ := K₀ * c + c ^ 2
  let b₂ := (1 + c) ^ 2
  let B := 1 + b₁ + b₂
  have hc : 0 < c := Real.exp_pos _
  have hb₁ : 0 ≤ b₁ := by dsimp only [b₁]; positivity
  have hb₂ : 0 ≤ b₂ := sq_nonneg _
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hb₁, hb₂]
  have hb₁B : b₁ ≤ B := by dsimp only [B]; linarith only [hb₂]
  have hb₂B : b₂ ≤ B := by dsimp only [B]; linarith only [hb₁]
  refine ⟨B, hB, ?_⟩
  intro Pi e ePlus hPi he hep hepbound
  have he0 : 0 ≤ e := zero_le_one.trans he
  have hPi0 : 0 ≤ Pi := zero_le_one.trans hPi
  have he2 : 1 ≤ e ^ 2 := by nlinarith only [he, sq_nonneg (e - 1)]
  have hprod : K₀ * e * ePlus ≤ (K₀ * c) * e ^ 2 := by
    calc
      _ ≤ K₀ * e * (c * e) := mul_le_mul_of_nonneg_left hepbound (by positivity)
      _ = _ := by ring
  have hsquare : ePlus ^ 2 ≤ c ^ 2 * e ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hep hepbound 2
  have hsum : (e + ePlus) ^ 2 ≤ b₂ * e ^ 2 := by
    have hh : e + ePlus ≤ (1 + c) * e := by linarith only [hepbound]
    simpa only [mul_pow, b₂] using pow_le_pow_left₀ (add_nonneg he0 hep) hh 2
  have hmajor (b : ℝ) (hb : b ≤ B) : 1 + Pi * (b * e ^ 2) ≤ B * ((2 + Pi) * e ^ 2) := by
    have hterm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (sq_nonneg e)) hPi0
    have hBe : 1 ≤ B * e ^ 2 := by nlinarith only [hB, he2, mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr he2)]
    nlinarith only [hterm, hBe]
  constructor
  · apply le_trans _ (hmajor b₁ hb₁B)
    apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hPi0)
    dsimp only [b₁]
    nlinarith only [hprod, hsquare]
  · exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hPi0)).trans (hmajor b₂ hb₂B)


end
end Homogenization.HighContrast.Annealed
