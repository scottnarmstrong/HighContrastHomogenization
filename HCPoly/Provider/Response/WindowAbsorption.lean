/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.WindowOmega

/-!
# The response-window choice order and the numerical absorption

The response window chooses, in the printed order
`e.response.transfer.tolerances`,
```
0 < ε_cal ≤ 1/3,   0 < δ_det ≤ 1,   H ∈ ℕ with H ≥ 4,
0 < η ≤ 1/2,       0 < η_dr ≤ min{1, η/2},
```
and makes those choices so that the numerical absorption closing the response
estimate,
```
12d ω_rsp(H, η, δ_det) R^{2d} (1 + δ_ad^{-1}) < 1,     R = 1 + δ_det,
```
holds.  The paper's existence proof is a three-limit argument:
`δ_det ↓ 0`, then `H ↑ ∞`, then — with that finite `H` fixed, so that the three
finite-window summation coefficients are fixed finite numbers — `η ↓ 0`.  It is reproduced here with explicit thresholds: the whole
`δ_det`-dependence of the printed constants runs through `R^{d/2}`, `R^{d/4}`
and `R^d`, all of which lie in `[1, 2^d]` on the admissible range, so the `H`
threshold can be taken uniform in `δ_det` and the printed order is respected a
fortiori.  No sign condition on `1/2 - ρ_max` is used.

`exists_response_window` is that statement, with every printed constant read off
its printed defining equation rather than named by a new definition: the
eighteen scalars — the universal, calibration, energy and profile constants of
the response estimate, its finite-window summation coefficients, its
recent-window constant, its bad-event constant, its weak-norm constant and the
coefficient of the terminal responses — are universally quantified after the
choice, each pinned by its display.  A consumer that has built its own
carriers for them discharges the absorption by supplying the eighteen equations.

The dimensional constant `C_d` of the passage from the terminal profiles to the
response bounds — the common enlargement of the dimensional constants of the
three response estimates, and *not*
the `C_d` the anchor's statement binds — is a plain universal parameter, so the
window may be chosen after it is known.  The target `δ_ad` is only asked to be
positive; the printed cap `δ_ad ≤ 1` is not used.
-/

namespace Homogenization
namespace HighContrast
namespace Response

noncomputable section

/-- **The response-window choice order with the numerical absorption** closing
the response estimate, in the order of `e.response.transfer.tolerances`.  The
five numbers are produced in the printed order and depend only on `(d, g, δ_ad)`
and on the dimensional
constant `C_d`; no coefficient law, aspect ratio, selected block or terminal
imbalance enters. -/
theorem exists_response_window {d : ℕ} (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {deltaAd : ℝ} (hAd : 0 < deltaAd) {Cd : ℝ} (hCd : 1 ≤ Cd) :
    ∃ (epsCal deltaDet : ℝ) (H : ℕ) (eta etaDr : ℝ),
      0 < epsCal ∧ epsCal ≤ 1 / 3 ∧ 0 < deltaDet ∧ deltaDet ≤ 1 ∧ 4 ≤ H ∧
        0 < eta ∧ eta ≤ 1 / 2 ∧ 0 < etaDr ∧ etaDr ≤ min 1 (eta / 2) ∧
        ∀ cconst GammaStar cepsStar betaStar chiTheta AStar TStar LStar KStar
          LenStar LambdaStar Scen Scell Sav UStar BStar RStar omegaRsp : ℝ,
          -- the universal constants of the response estimate
          cconst = (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ →
          GammaStar = 2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1 →
          -- its calibration constants
          cepsStar = Real.sqrt 2 →
          betaStar = cepsStar * (1 + deltaDet) ^ ((d : ℝ) / 2) →
          chiTheta = Real.sqrt (3 / 2) * (1 + deltaDet) ^ ((d : ℝ) / 2) →
          -- its energy constants
          AStar = 2 * chiTheta →
          TStar = 2 * ((1 + deltaDet) ^ (d : ℝ) - 1) * chiTheta →
          LStar = 32 * GammaStar * cepsStar * betaStar *
            (1 + deltaDet) ^ ((d : ℝ) / 2) * chiTheta →
          -- its profile constants
          KStar = Real.sqrt betaStar * (1 + deltaDet) ^ ((d : ℝ) / 4) →
          LenStar = 2 * Real.sqrt chiTheta →
          LambdaStar = Real.sqrt 5 * Real.sqrt chiTheta →
          -- its finite-window summation coefficients
          Scen = 2 * ∑ r ∈ Finset.range (H + 1),
            (3 : ℝ) ^ (-(1 / 2 - initExpRhoMax d g) * (r : ℝ)) →
          Scell = ∑ r ∈ Finset.Icc 1 H,
            (3 : ℝ) ^ (-(r : ℝ) / 2 + initExpA g * ((r : ℝ) - 1) / (initExpQ d g : ℝ)) →
          Sav = ∑ r ∈ Finset.Icc 1 H,
            (3 : ℝ) ^ (-initExpA g * (r : ℝ) +
              initExpA g * ((r : ℝ) - 1) / (2 * (initExpQ d g : ℝ))) →
          -- its recent-window and bad-event constants
          UStar = (Scen + Scell) * eta ^ ((initExpQ d g : ℝ)⁻¹) +
            Sav * eta ^ ((2 * (initExpQ d g : ℝ))⁻¹) →
          BStar = (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) * eta ^ ((2 : ℝ)⁻¹) →
          -- its weak-norm constant
          RStar = Cd * KStar * LenStar * UStar +
            Cd * KStar * Real.sqrt 2 * LambdaStar / (2 * initExpA g) *
              (BStar + (3 : ℝ) ^ (-initExpA g * (H : ℝ))) +
            cconst * KStar * LenStar * eta ^ ((initExpQ d g : ℝ)⁻¹) →
          -- the coefficient of the two terminal responses
          omegaRsp = 2 * Cd * (TStar + Real.sqrt (TStar * AStar) +
            Real.sqrt (TStar * LStar) +
            (3 : ℝ) ^ (-(H : ℝ)) * (AStar + Real.sqrt (AStar * LStar)) + RStar ^ 2) →
          -- the numerical absorption closing the response estimate
          12 * (d : ℝ) * omegaRsp * (1 + deltaDet) ^ (2 * (d : ℝ)) *
              (1 + deltaAd⁻¹) < 1 := by
  classical
  have hQpos : (0 : ℝ) < (initExpQ d g : ℝ) := zero_lt_initExpQ hd hg
  have ha : 0 < initExpA g := zero_lt_initExpA hg
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hM0 : (0 : ℝ) ≤ (2 : ℝ) ^ d := le_trans zero_le_one hM1
  have hAdinv : (0 : ℝ) < deltaAd⁻¹ := inv_pos.mpr hAd
  have hAd1 : (0 : ℝ) < 1 + deltaAd⁻¹ := by linarith only [hAdinv]
  have h12d : (0 : ℝ) < 12 * (d : ℝ) := by linarith only [hdR]
  set D : ℝ := 12 * (d : ℝ) * ((2 : ℝ) ^ d) ^ 2 * (1 + deltaAd⁻¹) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  set s : ℝ := 1 / (12 * Cd * D) with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hsq : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hspos
  -- the uniform coefficient majorant of the three summands of `𝓡_*`
  obtain ⟨W, hW0, hW1, hW2, hW3⟩ :
      ∃ W : ℝ, 0 ≤ W ∧ 8 * Cd * ((2 : ℝ) ^ d) ^ 3 ≤ W ∧ 24 * ((2 : ℝ) ^ d) ^ 3 ≤ W ∧
        24 * Cd * ((2 : ℝ) ^ d) ^ 3 ≤ W * (2 * initExpA g) := by
    refine ⟨(8 * Cd + 24) * ((2 : ℝ) ^ d) ^ 3 +
      12 * Cd * ((2 : ℝ) ^ d) ^ 3 / initExpA g, ?_, ?_, ?_, ?_⟩
    · positivity
    · have h2 : (0 : ℝ) ≤ 12 * Cd * ((2 : ℝ) ^ d) ^ 3 / initExpA g := by positivity
      have h3 : (0 : ℝ) ≤ 24 * ((2 : ℝ) ^ d) ^ 3 := by positivity
      linarith only [h2, h3]
    · have h2 : (0 : ℝ) ≤ 12 * Cd * ((2 : ℝ) ^ d) ^ 3 / initExpA g := by positivity
      have h3 : (0 : ℝ) ≤ 8 * Cd * ((2 : ℝ) ^ d) ^ 3 := by positivity
      linarith only [h2, h3]
    · have hexp : ((8 * Cd + 24) * ((2 : ℝ) ^ d) ^ 3 +
          12 * Cd * ((2 : ℝ) ^ d) ^ 3 / initExpA g) * (2 * initExpA g) =
          (8 * Cd + 24) * ((2 : ℝ) ^ d) ^ 3 * (2 * initExpA g) +
            24 * Cd * ((2 : ℝ) ^ d) ^ 3 := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (8 * Cd + 24) * ((2 : ℝ) ^ d) ^ 3 * (2 * initExpA g) := by
        positivity
      linarith only [hexp, hnn]
  -- FIRST LIMIT (`δ_det ↓ 0`): the determinant slack
  obtain ⟨tau0, htau0, htauS, htauQ⟩ :
      ∃ tau0 : ℝ, 0 < tau0 ∧ tau0 ≤ s ∧ 1024 * ((2 : ℝ) ^ d) ^ 3 * tau0 ≤ s ^ 2 := by
    refine ⟨min s (s ^ 2 / (1024 * ((2 : ℝ) ^ d) ^ 3)), lt_min hspos (by positivity),
      min_le_left _ _, ?_⟩
    have hden : (0 : ℝ) < 1024 * ((2 : ℝ) ^ d) ^ 3 := by positivity
    have := (le_div_iff₀ hden).mp (min_le_right s (s ^ 2 / (1024 * ((2 : ℝ) ^ d) ^ 3)))
    linarith only [this]
  obtain ⟨delta, hdelta0, hdelta1, hdeltaT⟩ :
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ 4 * ((2 : ℝ) ^ d) ^ 2 * delta ≤ tau0 := by
    have hden : (0 : ℝ) < 4 * ((2 : ℝ) ^ d) ^ 2 := by positivity
    refine ⟨min 1 (tau0 / (4 * ((2 : ℝ) ^ d) ^ 2)), lt_min zero_lt_one (by positivity),
      min_le_left _ _, ?_⟩
    have h := mul_le_mul_of_nonneg_left
      (min_le_right 1 (tau0 / (4 * ((2 : ℝ) ^ d) ^ 2))) hden.le
    rw [mul_div_cancel₀ _ (ne_of_gt hden)] at h
    linarith only [h]
  -- SECOND LIMIT (`H ↑ ∞`): the two lower-edge terms
  obtain ⟨H, hH4, hHedge, hHrow⟩ :
      ∃ H : ℕ, 4 ≤ H ∧ 68 * ((2 : ℝ) ^ d) ^ 2 * ((1 : ℝ) / 3) ^ H ≤ s ∧
        W * ((3 : ℝ) ^ (-initExpA g)) ^ H ≤ Real.sqrt s / 2 := by
    obtain ⟨N1, hN1⟩ := exists_nat_forall_mul_pow_le (c := 68 * ((2 : ℝ) ^ d) ^ 2)
      (r := (1 : ℝ) / 3) (target := s) (by positivity) (by norm_num) (by norm_num) hspos
    obtain ⟨N2, hN2⟩ := exists_nat_forall_mul_pow_le (c := W)
      (r := (3 : ℝ) ^ (-initExpA g)) (target := Real.sqrt s / 2) hW0
      (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ha]))
      (by linarith only [hsq])
    exact ⟨max 4 (max N1 N2), le_max_left _ _,
      hN1 _ (le_trans (le_max_left N1 N2) (le_max_right _ _)),
      hN2 _ (le_trans (le_max_right N1 N2) (le_max_right _ _))⟩
  -- THIRD LIMIT (`η ↓ 0`): the three finite-window sums are now fixed
  obtain ⟨Sfull, hSfull0, hSfullEq⟩ :
      ∃ S : ℝ, 0 ≤ S ∧ S =
        2 * ∑ r ∈ Finset.range (H + 1),
            (3 : ℝ) ^ (-(1 / 2 - initExpRhoMax d g) * (r : ℝ)) +
          (∑ r ∈ Finset.Icc 1 H,
            (3 : ℝ) ^ (-(r : ℝ) / 2 +
              initExpA g * ((r : ℝ) - 1) / (initExpQ d g : ℝ))) +
          ∑ r ∈ Finset.Icc 1 H,
            (3 : ℝ) ^ (-initExpA g * (r : ℝ) +
              initExpA g * ((r : ℝ) - 1) / (2 * (initExpQ d g : ℝ))) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨eta, heta0, heta1, hetakey⟩ :=
    exists_eta_mul_rpow_le
      (c := W * (Sfull + (2 : ℝ) ^ ((initExpQ d g : ℝ) / 2) + 1))
      (r := Real.sqrt s / 2) (p := (2 * (initExpQ d g : ℝ))⁻¹)
      (by positivity) (by linarith only [hsq]) (by positivity)
  -- the window, in the printed order
  refine ⟨1 / 3, delta, H, eta, min 1 (eta / 2), by norm_num, le_refl _, hdelta0,
    hdelta1, hH4, heta0, heta1, lt_min zero_lt_one (by linarith only [heta0]),
    le_refl _, ?_⟩
  intro cconst GammaStar cepsStar betaStar chiTheta AStar TStar LStar KStar LenStar
    LambdaStar Scen Scell Sav UStar BStar RStar omegaRsp hcconst hGamma hceps hbeta
    hchi hAstar hTstar hLstar hKstar hLen hLam hScen hScell hSav hUstar hBstar
    hRstar homega
  obtain ⟨hcc1, hcc3⟩ := cconst_bounds hcconst
  obtain ⟨hA1, hA2⟩ := aStar_bounds hdelta0.le hdelta1 hchi hAstar
  obtain ⟨hT1, hT2⟩ := tStar_bounds hdelta0.le hdelta1 hchi hTstar
  obtain ⟨hL1, hL2⟩ := lStar_bounds hdelta0.le hdelta1 hGamma hceps hbeta hchi hLstar
  obtain ⟨hK1, hK2⟩ := kStar_bounds hdelta0.le hdelta1 hceps hbeta hKstar
  obtain ⟨hLen1, hLen2⟩ := lenStar_bounds hdelta0.le hdelta1 hchi hLen
  obtain ⟨hLam1, hLam2⟩ := lambdaStar_bounds hdelta0.le hdelta1 hchi hLam
  have hSsum : Scen + Scell + Sav = Sfull := by rw [hScen, hScell, hSav, hSfullEq]
  obtain ⟨_, hterm5⟩ :=
    rStar_le_sqrt hd hg hCd hcc1 hcc3 hK1 hK2 hLen1 hLen2 hLam1 hLam2 heta0 heta1
      hspos hW0 hW1 hW2 hW3 (by rw [hScen]; positivity) (by rw [hScell]; positivity)
      (by rw [hSav]; positivity) hSsum hUstar hBstar hRstar hHrow hetakey
  obtain ⟨homega0, homegaLe⟩ :=
    omega_le_of_slack hCd hspos htau0 htauS htauQ hT1 hT2 hdeltaT hA1 hA2 hL1 hL2
      hHedge hterm5 homega
  -- the absorption
  have hDs : 12 * Cd * D * s = 1 := by rw [hs]; field_simp
  have hfinal : D * omegaRsp ≤ 10 / 12 := by
    have h1 : D * omegaRsp ≤ D * (10 * Cd * s) :=
      mul_le_mul_of_nonneg_left homegaLe hDpos.le
    have h2 : D * (10 * Cd * s) = 10 / 12 * (12 * Cd * D * s) := by ring
    rw [h2, hDs] at h1
    linarith only [h1]
  have hR2d : (1 + delta) ^ (2 * (d : ℝ)) ≤ ((2 : ℝ) ^ d) ^ 2 :=
    rpow_one_add_two_mul_le hdelta0.le hdelta1
  have hcoefnn : (0 : ℝ) ≤ 12 * (d : ℝ) * (1 + deltaAd⁻¹) * omegaRsp :=
    mul_nonneg (by positivity) homega0
  calc 12 * (d : ℝ) * omegaRsp * (1 + delta) ^ (2 * (d : ℝ)) * (1 + deltaAd⁻¹)
      = 12 * (d : ℝ) * (1 + deltaAd⁻¹) * omegaRsp * (1 + delta) ^ (2 * (d : ℝ)) := by
        ring
    _ ≤ 12 * (d : ℝ) * (1 + deltaAd⁻¹) * omegaRsp * ((2 : ℝ) ^ d) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2d hcoefnn
    _ = D * omegaRsp := by rw [hD]; ring
    _ ≤ 10 / 12 := hfinal
    _ < 1 := by norm_num

end

end Response
end HighContrast
end Homogenization
