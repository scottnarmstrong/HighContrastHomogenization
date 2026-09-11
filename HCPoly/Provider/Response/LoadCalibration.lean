/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.LoadCalibrationClosure

/-!
# The response-load calibration — the deterministic core

The assembly of the calibration of the response loads used in
`p.response.transfer`.  This file collects the boxed displays that are
consequences of the printed data alone, under exactly the printed hypotheses:

* positive doubled blocks `E⁰, E_s, E_t` with `E_t ≤ E_s`, `E_s^♯ ≤ E_s`,
  `E_t^♯ ≤ E_t`, and the near-isometry `(1-ε_cal)E⁰ ≤ E_s ≤ (1+ε_cal)E⁰`;
* `c_ε = ((1+ε_cal)/(1-ε_cal))^{1/2}`, `ϱ = (det E_s/det E_t)^{1/d}`,
  `β = c_ε ϱ^{d/2}`;
* the unique Schur form `E_t = schurBlock S S_* K` and the response
  coordinates `h = ½(K - Kᵗ)`, `r = ½(K + Kᵗ)`, `B = S + rᵗS_*⁻¹r`,
  `m = B # S_*`, `θ = |S_*^{-1/2}BS_*^{-1/2}|`;
* the canonical factors `m₀ = m(E⁰)`, `g₀ = g(E⁰)`, and
  `𝐆₀ = G_{g₀}`, `𝐌₀ = diag(m₀, m₀⁻¹)`, `Ê_u = 𝐆₀ᵗE_u𝐆₀`;
* a unit vector `e`, and `p = m^{-1/2}e`, `q = m^{1/2}e`.

The displays that also consume an annealed input — the two centers
([Armstrong–Kuusi, (2.32)]), the annealed energy identity, the corrected absolute
response estimate, and the terminal-profile compatibility clause — are proved
in `LoadCalibrationCenters` and `LoadCalibrationClosure` with that input
carried in its printed shape, and are composed with this core there.

There are no definitions in this file.
-/

namespace Homogenization
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- **The response-load calibration, the deterministic core.**  Under the
printed hypotheses, the calibrated sandwich, the two imbalance comparisons, the
response-ratio calibration, the exact energy sum with its bound, the two
individual load bounds, the two canonical balance chains, and the two signed
loads in the canonical metric. -/
theorem response_load_calibration (hd : 2 ≤ d)
    {E0 Es Et : FullBlockMat d} (hE0 : E0.PosDef) (hEs : Es.PosDef) (hEt : Et.PosDef)
    (hts : Et ≤ Es) (hsSharp : fullBlockSharp Es ≤ Es) (htSharp : fullBlockSharp Et ≤ Et)
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    (hlow : (1 - eps) • E0 ≤ Es) (hhigh : Es ≤ (1 + eps) • E0)
    {ceps rho beta : ℝ} (hceps : ceps = Real.sqrt ((1 + eps) / (1 - eps)))
    (hrho : rho = canonDetRatio Es Et) (hbeta : beta = ceps * Real.sqrt (rho ^ d))
    {S SStar K r B m g0 m0 h : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hEtform : Et = schurBlock S SStar K)
    (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) (hh : h = (2 : ℝ)⁻¹ • (K - Kᴴ))
    (hB : B = S + rᴴ * SStar⁻¹ * r) (hmdef : m = matGeomMean B SStar)
    (hg0 : g0 = canonShear E0) (hm0 : m0 = canonMetric E0)
    {G0 M0 Ehat Eshat : FullBlockMat d}
    (hG0 : G0 = fullBlockShear g0) (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹)
    (hEhat : Ehat = G0ᴴ * Et * G0) (hEshat : Eshat = G0ᴴ * Es * G0)
    {e p q : Vec d} (he : e ⬝ᵥ e = 1) (hp : p = matSqrt m⁻¹ *ᵥ e)
    (hq : q = matSqrt m *ᵥ e) :
    (beta⁻¹ • M0 ≤ G0ᴴ * canonBlock Et * G0 ∧
        G0ᴴ * canonBlock Et * G0 ≤ beta • M0) ∧
      (canonImbalance Et ≤ rho ^ d * canonImbalance Es ∧
        canonImbalance Es ≤ rho ^ (2 * d) * canonImbalance Et) ∧
      (1 ≤ relSize B SStar ∧
        relSize B SStar ≤ (3 * canonImbalance Et - 1) / 2 ∧
        canonImbalance Et - 1 ≤ 6 * (relSize B SStar - 1)) ∧
      (Sum.elim (-p) (q + (g0 - h) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim (-p) (q + (g0 - h) *ᵥ p) +
          Sum.elim p (q + (h - g0) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim p (q + (h - g0) *ᵥ p) =
        4 * (e ⬝ᵥ (matSqrt m * SStar⁻¹ * matSqrt m) *ᵥ e)) ∧
      (Sum.elim (-p) (q + (g0 - h) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim (-p) (q + (g0 - h) *ᵥ p) ≤
          4 * Real.sqrt (relSize B SStar) ∧
        Sum.elim p (q + (h - g0) *ᵥ p) ⬝ᵥ Ehat *ᵥ Sum.elim p (q + (h - g0) *ᵥ p) ≤
          4 * Real.sqrt (relSize B SStar)) ∧
      (beta⁻¹ • M0 ≤ Ehat ∧ Ehat ≤ (beta * Real.sqrt (canonImbalance Et)) • M0) ∧
      Eshat ≤ (ceps * Real.sqrt (canonImbalance Es)) • M0 ∧
      (Sum.elim (-p) (q + (g0 - h) *ᵥ p) ⬝ᵥ M0 *ᵥ Sum.elim (-p) (q + (g0 - h) *ᵥ p) ≤
          4 * beta * Real.sqrt (relSize B SStar) ∧
        Sum.elim p (q + (h - g0) *ᵥ p) ⬝ᵥ M0 *ᵥ Sum.elim p (q + (h - g0) *ᵥ p) ≤
          4 * beta * Real.sqrt (relSize B SStar)) := by
  haveI : NeZero d := ⟨by omega⟩
  -- the Schur form of the terminal block
  have htSharp' : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K := by
    rw [← hEtform]; exact htSharp
  -- the shear and the metric block, in the shape the geometry layer expects
  have hG0' : G0 = fullBlockShear (canonShear E0) := by rw [hG0, hg0]
  have hM0' : M0 = Matrix.fromBlocks (canonMetric E0) 0 0 (canonMetric E0)⁻¹ := by
    rw [hM0, hm0]
  -- positivity of the calibration scalars
  have hm : (0 : ℝ) < 1 - eps := by linarith only [heps1]
  have hpe : (0 : ℝ) < 1 + eps := by linarith only [heps0]
  have hcpos : 0 < ceps := by rw [hceps]; exact Real.sqrt_pos.mpr (div_pos hpe hm)
  have hdetpos : (0 : ℝ) < Es.det / Et.det := div_pos hEs.det_pos hEt.det_pos
  have hrpow : rho ^ d = Es.det / Et.det := by
    rw [hrho]; exact canonDetRatio_pow (by omega) hdetpos.le
  have hspos : 0 < Real.sqrt (rho ^ d) := by rw [hrpow]; exact Real.sqrt_pos.mpr hdetpos
  have hbpos : 0 < beta := by rw [hbeta]; exact mul_pos hcpos hspos
  -- the response ratio
  have hthetaOne : 1 ≤ relSize B SStar := one_le_response_ratio hS hStar hB htSharp'
  have hthetaPos : 0 < relSize B SStar := lt_of_lt_of_le one_pos hthetaOne
  have hBle : B ≤ relSize B SStar • SStar :=
    le_relSize_smul (posSemidef_responseBlock hS hStar hB) hStar
  refine ⟨metric_sandwich hd hE0 hEs hEt hts heps0 heps1 hlow hhigh hceps hrho hbeta
      hG0' hM0', imbalance_comparisons hd hEs hEt hts hrho, ⟨hthetaOne, ?_, ?_⟩, ?_, ⟨?_, ?_⟩,
    ?_, ?_, ⟨?_, ?_⟩⟩
  · have h := response_ratio_le_printed hS hStar hr hB htSharp'
    rwa [← hEtform] at h
  · have h := canonImbalance_le_one_add_six_mul_sub_one hS hStar hr hB htSharp'
    rw [← hEtform] at h
    linarith only [h]
  · exact load_sum_eq hS hStar hEtform hG0 hEhat hr hh hB hmdef hp hq
  · exact load_sq_neg_le hS hStar hEt hEtform hG0 hEhat hr hh hB hmdef hp hq he
      hthetaPos hBle
  · exact load_sq_pos_le hS hStar hEt hEtform hG0 hEhat hr hh hB hmdef hp hq he
      hthetaPos hBle
  · have h := hatE_terminal_sandwich hd hE0 hEs hEt hts htSharp heps0 heps1 hlow hhigh
      hceps hrho hbeta hG0' hM0'
    rw [← hEhat] at h
    exact h
  · have h := hatE_earlier_bound hE0 hEs hsSharp heps0 heps1 hlow hhigh hceps hG0' hM0'
    rw [← hEshat] at h
    exact h
  · obtain ⟨hlowE, -⟩ := hatE_terminal_sandwich hd hE0 hEs hEt hts htSharp heps0 heps1
      hlow hhigh hceps hrho hbeta hG0' hM0'
    rw [← hEhat] at hlowE
    exact metric_signed_load_le hbpos hlowE
      (load_sq_neg_le hS hStar hEt hEtform hG0 hEhat hr hh hB hmdef hp hq he
        hthetaPos hBle)
  · obtain ⟨hlowE, -⟩ := hatE_terminal_sandwich hd hE0 hEs hEt hts htSharp heps0 heps1
      hlow hhigh hceps hrho hbeta hG0' hM0'
    rw [← hEhat] at hlowE
    exact metric_signed_load_le hbpos hlowE
      (load_sq_pos_le hS hStar hEt hEtform hG0 hEhat hr hh hB hmdef hp hq he
        hthetaPos hBle)

end

end Response
end HighContrast
end Homogenization
