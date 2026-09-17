import HCPoly.Entry.Annealed.TransportProfileComparison
import HCPoly.Entry.Annealed.TransportEndpointBounds
open Homogenization.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace Homogenization.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- Transport of the complete profile with the single printed constant. -/
theorem two_grid_transport_roundedGrid
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ρ : ℝ, ρ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
          ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : CoeffSpace d → ℝ),
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K S →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                  ∀ L : ℕ,
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    C * ((L : ℝ) +
                        Real.logb 3 ((2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖))) ≤
                      (n : ℝ) - (jStar : ℝ) →
                    projectiveDistance m mPlus ≤ 1 →
                    C + Real.logb 3 ρ⁻¹ ≤ (L : ℝ) →
                    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                          (n + 2 * (L : ℤ)) ≤
                      (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (L : ℝ)) * ρ →
                    BlockMatLoewnerLE
                        (blockScale (1 - δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
                    BlockMatLoewnerLE
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                        (blockScale (1 + δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))) →
                    profile P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ))
                          (n + (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                          (n + (L : ℤ)) ≤
                      C * (δ + ρ) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨K₀, hK₀, hgrid⟩ := exists_transport_grid_constant d hd
  obtain ⟨Cps, Cp, hCps, hCp, hprofile⟩ := exists_two_grid_profile_comparison d hd K₀ hK₀ γ hγ
  obtain ⟨Cds, Cd, hCds, hCd, hdrift⟩ := exists_two_grid_drift_comparison d hd K₀ hK₀ γ hγ
  obtain ⟨B, hB, hbrackets⟩ := transport_source_brackets K₀ hK₀
  let a := (1 - γ) / 8
  let Q := bigQ d γ
  have ha : 0 < a := by dsimp only [a]; linarith only [hγ.2]
  obtain ⟨Csep, Cpoly, hCsep, hCpoly, habsorb⟩ :=
    exists_transport_source_absorption a (Q : ℝ) ha (Nat.cast_nonneg Q)
  let Ct := Cp + Cd + Cp * B ^ Q + Cd * K₀ + Cd * B * Cpoly
  let C := max 1 (max Csep Ct)
  have hC : 1 ≤ C := le_max_left _ _
  have hsepC : Csep ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have htC : Ct ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hct : Cp + Cd ≤ Ct := by
    have h₁ : 0 ≤ Cp * B ^ Q := by positivity
    have h₂ : 0 ≤ Cd * K₀ := by positivity
    have h₃ : 0 ≤ Cd * B * Cpoly := by positivity
    dsimp only [Ct]
    linarith only [h₁, h₂, h₃]
  refine ⟨C, hC, max Cps Cds, hCps.trans_le (le_max_left _ _), ?_⟩
  intro ρ hρ δ hδ P hP E Ψ K S hstat hunit hdag jStar hj hsrc m mPlus hm hmPlus k n hk hkn L
    hwindow hsep hpr hlength hsmall hlow hup
  obtain ⟨hL, hdecay⟩ := transport_length_decay C ρ hC hρ L hlength
  obtain ⟨hratio, hePlus, he⟩ := hgrid jStar hj m mPlus hm hmPlus hpr
  have hlogK : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by have := hdag.one_lt_growthWitness; linarith : (1 : ℝ) < 2 * K)).le
  have hsP := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cps Cds) hlogK)).trans hsrc
  have hsD := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cps Cds) hlogK)).trans hsrc
  have hp := hprofile P E Ψ K S hstat hunit hdag jStar hj hsP m mPlus hm hmPlus hratio
    k n hk hkn L hL hwindow δ hδ hlow hup
  have hD := hdrift P E Ψ K S hstat hdag jStar hj hsD m mPlus hm hmPlus hratio
    n (hk.trans hkn) L hL hwindow δ hδ hlow hup
  let A := (2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖)
  let x := (n : ℝ) - jStar
  have hPi : 1 ≤ aspectRatio E := one_le_aspectRatio hdag
  have hnrm : 1 ≤ ‖m‖ * ‖m⁻¹‖ := one_le_norm_mul_norm_inv hm
  have hA : 1 ≤ A := by
    dsimp only [A]
    nlinarith only [hPi, hnrm, mul_nonneg (sub_nonneg.mpr hPi) (sub_nonneg.mpr hnrm)]
  have hlogA : 0 ≤ Real.logb 3 A := Real.logb_nonneg (by norm_num) hA
  have hsep' : Csep * ((L : ℝ) + Real.logb 3 A) ≤ x :=
    (mul_le_mul_of_nonneg_right hsepC (add_nonneg (Nat.cast_nonneg L) hlogA)).trans hsep
  obtain ⟨hsourceP, hsourceD⟩ := habsorb A L x hA (Nat.cast_nonneg L) hsep'
  have heq : Real.sqrt (‖m‖ * ‖m⁻¹‖) ^ 2 = ‖m‖ * ‖m⁻¹‖ := Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  obtain ⟨hbP, hbD⟩ := hbrackets (aspectRatio E) (Real.sqrt (‖m‖ * ‖m⁻¹‖))
    (Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) hPi he (Real.sqrt_nonneg _) hePlus
  rw [heq] at hbP hbD
  have hsourceP' : A ^ Q * (3 : ℝ) ^ (-((1 - γ) / 4) * x) ≤ (3 : ℝ) ^ (-(L : ℝ)) := by
    have hexa : 2 * a = (1 - γ) / 4 := by dsimp only [a]; ring
    simpa only [Real.rpow_natCast, hexa] using hsourceP
  have hpayP : Cp * (1 + aspectRatio E *
      (K₀ * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) +
        Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ^ 2)) ^ Q *
          (3 : ℝ) ^ (-((1 - γ) / 4) * x) ≤ Cp * B ^ Q * ρ := by
    calc
      _ ≤ Cp * (B * A) ^ Q * (3 : ℝ) ^ (-((1 - γ) / 4) * x) := by
        gcongr
      _ = (Cp * B ^ Q) * (A ^ Q * (3 : ℝ) ^ (-((1 - γ) / 4) * x)) := by rw [mul_pow]; ring
      _ ≤ (Cp * B ^ Q) * (3 : ℝ) ^ (-(L : ℝ)) := mul_le_mul_of_nonneg_left hsourceP' (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)
  have hx : 0 ≤ x := by dsimp only [x]; exact_mod_cast (sub_nonneg.mpr (hk.trans hkn))
  have hpayD : Cd * (1 + aspectRatio E *
      (Real.sqrt (‖m‖ * ‖m⁻¹‖) + Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖)) ^ 2) *
        (1 + (n : ℝ) + L - jStar) * (3 : ℝ) ^ (-a * x) ≤ Cd * B * Cpoly * ρ := by
    calc
      _ ≤ Cd * (B * A) * (1 + x + L) * (3 : ℝ) ^ (-a * x) := by
        have hfac : 0 ≤ 1 + x + L := by positivity
        have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbD hCd.le) hfac) (by positivity : 0 ≤ (3 : ℝ) ^ (-a * x))
        convert hh using 1 <;> try rfl
        dsimp only [x]
        ring
      _ = (Cd * B) * (A * (1 + x + L) * (3 : ℝ) ^ (-a * x)) := by ring
      _ ≤ (Cd * B) * (Cpoly * (3 : ℝ) ^ (-(L : ℝ))) := mul_le_mul_of_nonneg_left hsourceD (by positivity)
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdecay (by positivity : 0 ≤ Cd * B * Cpoly)
  have hp0 := bridge_profile_nonneg d hd P γ hγ E Ψ K S hstat hdag jStar hj m hm
    k (n + 2 * (L : ℤ)) hk (by omega)
  have hD0 := bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm (n + 2 * (L : ℤ))
  have hw := transport_weighted_smallness γ _ _ ρ L hγ.2 (Nat.cast_nonneg L) hp0 hD0 hsmall
  have hpbound := mul_le_mul_of_nonneg_left hw.2.1 hCp.le
  have hDbound := mul_le_mul_of_nonneg_left hw.2.2 hCd.le
  have hKd := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hCd.le (zero_le_one.trans hK₀))
  have hfinal : profile P γ (explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ)) (n + (L : ℤ)) +
      determinantDrift P γ (explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ)) ≤ Ct * (δ + ρ) := by
    have hδpay := mul_le_mul_of_nonneg_right hct hδ.1
    dsimp only [Ct] at hδpay ⊢
    change _ ≤ Cd * (δ + K₀ * (3 : ℝ) ^ (-(L : ℝ)) +
      (3 : ℝ) ^ ((1 - γ) / 4 * (L : ℝ)) * _) + _ at hD
    dsimp only [a, x, Q] at hpayP hpayD
    nlinarith only [hp, hD, hpayP, hpayD, hpbound, hDbound, hKd, hδpay]
  exact hfinal.trans (mul_le_mul_of_nonneg_right htC (add_nonneg hδ.1 hρ.1.le))

end
end Homogenization.HighContrast.Annealed
