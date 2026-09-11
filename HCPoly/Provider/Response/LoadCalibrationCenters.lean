/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.LoadCalibrationProfile

/-!
# The two independently computed centers and the earlier-scale row loads

Two of the boxed displays of the response-load calibration:

    |𝐌₀^{1/2}Y^±|² ≤ 8β(√κ_t + 1)√θ,
    𝒬_s^± ≤ 8c_ε β √κ_s (√κ_t + 1)√θ.

The printed proof computes the two centers independently from
the mean-response identity [Armstrong–Kuusi, (2.32)] — the primal one for the
primal field, the adjoint one afresh for the coefficient-transpose field — and
finds

    Y^- = (I + 𝐑Ê_t)x^-,       Y^+ = (I - 𝐑Ê_t)x^+,

with `𝐑 = (0 I; I 0)`.  This file takes that identity in its printed shape: the
centers are annealed averages of solution fields, whose identification belongs
to the profile layer, and only the *bound* is calibration.  Given the identity,
the estimate is deterministic:

    |𝐌₀^{1/2}Y|² ≤ 2|𝐌₀^{1/2}x|² + 2|𝐌₀^{-1/2}Ê_tx|²
                 ≤ 2β(L)² + 2β√κ_t(L)²,

where the first step is `𝐑𝐌₀𝐑 = 𝐌₀⁻¹` together with polarization, and the
second uses `Ê_t𝐌₀⁻¹Ê_t ≤ β√κ_t Ê_t`, which follows from the upper canonical
comparison `Ê_t ≤ β√κ_t 𝐌₀` by order reversal and congruence.

For `𝒬_s^±` the two block coordinate projections of the center are read against
`Ê_s ≤ c_ε√κ_s 𝐌₀`; since `𝐌₀` is block diagonal, the two projected
`𝐌₀`-energies add up to the full one.

There are no definitions in this file.
-/

namespace Homogenization
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The reflection and the canonical metric block -/

/-- **`𝐑𝐌₀𝐑 = 𝐌₀⁻¹`**. -/
theorem refl_conj_metricBlock {m0 : Mat d} (hm0 : m0.PosDef) {M0 : FullBlockMat d}
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) :
    (fullBlockRefl d)ᴴ * M0 * fullBlockRefl d = M0⁻¹ := by
  have hu : IsUnit m0.det := isUnit_det_of_posDef hm0
  have hinv : M0⁻¹ = Matrix.fromBlocks m0⁻¹ 0 0 m0 := by
    rw [hM0]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, Matrix.fromBlocks_one]
  rw [hinv, hM0, conjTranspose_fullBlockRefl, fullBlockRefl, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

/-! ## Two quadratic-form consequences -/

/-- The quadratic form of a positive semidefinite matrix is subadditive up to a
factor two. -/
theorem quadratic_add_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (u v : n → ℝ) :
    (u + v) ⬝ᵥ A *ᵥ (u + v) ≤ 2 * (u ⬝ᵥ A *ᵥ u) + 2 * (v ⬝ᵥ A *ᵥ v) := by
  have hpol := polarization A u v
  have hnn := quadratic_nonneg hA (u - v)
  linarith only [hpol, hnn]

/-- The quadratic form of a positive semidefinite matrix is subadditive up to a
factor two, in the subtracted form. -/
theorem quadratic_sub_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (u v : n → ℝ) :
    (u - v) ⬝ᵥ A *ᵥ (u - v) ≤ 2 * (u ⬝ᵥ A *ᵥ u) + 2 * (v ⬝ᵥ A *ᵥ v) := by
  have hpol := polarization A u v
  have hnn := quadratic_nonneg hA (u + v)
  linarith only [hpol, hnn]

/-- **`AM⁻¹A ≤ cA` from `A ≤ cM`**, by order reversal and
congruence by `A`. -/
theorem sandwich_inv {n : Type*} [Fintype n] [DecidableEq n] {A M : Matrix n n ℝ}
    (hA : A.PosDef) (hM : M.PosDef) {c : ℝ} (hc : 0 < c) (h : A ≤ c • M) :
    A * M⁻¹ * A ≤ c • A := by
  have hinv := inv_le_inv_of_le hA (posDef_smul hM hc) h
  rw [inv_smul_posDef hM hc] at hinv
  have hconj := conj_le_conj' (C := A) hA.isHermitian hinv
  have hAA : A * A⁻¹ * A = A := by
    rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hA), Matrix.one_mul]
  rw [Matrix.mul_smul, Matrix.smul_mul, hAA] at hconj
  exact le_of_smul_inv_le hc hconj

/-! ## The centers -/

variable {m0 : Mat d} {Ehat M0 : FullBlockMat d}

/-- **The reflected image in the canonical metric**:
`|𝐌₀^{1/2}𝐑Ê_tx|² = x ⬝ Ê_t𝐌₀⁻¹Ê_t x`. -/
theorem metric_refl_image (hm0 : m0.PosDef)
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) (hsymm : Ehatᴴ = Ehat)
    (x : FullBlockVec d) :
    (fullBlockRefl d *ᵥ (Ehat *ᵥ x)) ⬝ᵥ M0 *ᵥ (fullBlockRefl d *ᵥ (Ehat *ᵥ x)) =
      x ⬝ᵥ (Ehat * M0⁻¹ * Ehat) *ᵥ x := by
  rw [← Initialization.quad_conj (fullBlockRefl d) M0 (Ehat *ᵥ x),
    refl_conj_metricBlock hm0 hM0, ← Initialization.quad_conj Ehat M0⁻¹ x, hsymm]

/-- **The center bound** `|𝐌₀^{1/2}Y^±|² ≤ 8β(√κ_t + 1)√θ`,
given the printed center identity `Y = x ± 𝐑Ê_tx`. -/
theorem metric_center_le (hm0 : m0.PosDef)
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) (hEhatPd : Ehat.PosDef)
    {beta kappa theta : ℝ} (hbeta : 0 < beta) (hkappa : 0 < kappa)
    (hlow : beta⁻¹ • M0 ≤ Ehat) (hup : Ehat ≤ (beta * Real.sqrt kappa) • M0)
    {x Y : FullBlockVec d} (hY : Y = x + fullBlockRefl d *ᵥ (Ehat *ᵥ x))
    (hx : x ⬝ᵥ Ehat *ᵥ x ≤ 4 * Real.sqrt theta) :
    Y ⬝ᵥ M0 *ᵥ Y ≤ 8 * beta * (Real.sqrt kappa + 1) * Real.sqrt theta := by
  have hM0pd : M0.PosDef := by rw [hM0]; exact posDef_metricBlock hm0
  have hsplit : Y ⬝ᵥ M0 *ᵥ Y ≤
      2 * (x ⬝ᵥ M0 *ᵥ x) +
        2 * ((fullBlockRefl d *ᵥ (Ehat *ᵥ x)) ⬝ᵥ M0 *ᵥ (fullBlockRefl d *ᵥ (Ehat *ᵥ x))) := by
    rw [hY]
    exact quadratic_add_le hM0pd.posSemidef _ _
  rw [metric_refl_image hm0 hM0 hEhatPd.isHermitian x] at hsplit
  -- the two terms
  have hterm₁ : x ⬝ᵥ M0 *ᵥ x ≤ beta * (x ⬝ᵥ Ehat *ᵥ x) := metric_load_le_smul hbeta hlow x
  have hterm₂ : x ⬝ᵥ (Ehat * M0⁻¹ * Ehat) *ᵥ x ≤
      (beta * Real.sqrt kappa) * (x ⬝ᵥ Ehat *ᵥ x) := by
    have h := Initialization.dotProduct_mulVec_le_of_le
      (sandwich_inv hEhatPd hM0pd
        (mul_pos hbeta (Real.sqrt_pos.mpr hkappa)) hup) x
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    exact h
  have hnn : 0 ≤ x ⬝ᵥ Ehat *ᵥ x := quadratic_nonneg hEhatPd.posSemidef x
  have hfac : 0 ≤ 2 * beta * (Real.sqrt kappa + 1) := by positivity
  have hstep : 2 * (x ⬝ᵥ M0 *ᵥ x) + 2 * (x ⬝ᵥ (Ehat * M0⁻¹ * Ehat) *ᵥ x) ≤
      2 * beta * (Real.sqrt kappa + 1) * (x ⬝ᵥ Ehat *ᵥ x) := by
    linarith only [hterm₁, hterm₂]
  have hfinal := mul_le_mul_of_nonneg_left hx hfac
  linarith only [hsplit, hstep, hfinal]

/-- **The center bound, adjoint sign** `|𝐌₀^{1/2}Y^+|² ≤ 8β(√κ_t + 1)√θ`, given the printed center identity `Y^+ = (I - 𝐑Ê_t)x^+`.  The
adjoint center is computed afresh, not copied from the primal one. -/
theorem metric_center_le_sub (hm0 : m0.PosDef)
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) (hEhatPd : Ehat.PosDef)
    {beta kappa theta : ℝ} (hbeta : 0 < beta) (hkappa : 0 < kappa)
    (hlow : beta⁻¹ • M0 ≤ Ehat) (hup : Ehat ≤ (beta * Real.sqrt kappa) • M0)
    {x Y : FullBlockVec d} (hY : Y = x - fullBlockRefl d *ᵥ (Ehat *ᵥ x))
    (hx : x ⬝ᵥ Ehat *ᵥ x ≤ 4 * Real.sqrt theta) :
    Y ⬝ᵥ M0 *ᵥ Y ≤ 8 * beta * (Real.sqrt kappa + 1) * Real.sqrt theta := by
  have hM0pd : M0.PosDef := by rw [hM0]; exact posDef_metricBlock hm0
  have hsplit : Y ⬝ᵥ M0 *ᵥ Y ≤
      2 * (x ⬝ᵥ M0 *ᵥ x) +
        2 * ((fullBlockRefl d *ᵥ (Ehat *ᵥ x)) ⬝ᵥ M0 *ᵥ
          (fullBlockRefl d *ᵥ (Ehat *ᵥ x))) := by
    rw [hY]
    exact quadratic_sub_le hM0pd.posSemidef _ _
  rw [metric_refl_image hm0 hM0 hEhatPd.isHermitian x] at hsplit
  have hterm₁ : x ⬝ᵥ M0 *ᵥ x ≤ beta * (x ⬝ᵥ Ehat *ᵥ x) := metric_load_le_smul hbeta hlow x
  have hterm₂ : x ⬝ᵥ (Ehat * M0⁻¹ * Ehat) *ᵥ x ≤
      (beta * Real.sqrt kappa) * (x ⬝ᵥ Ehat *ᵥ x) := by
    have h := Initialization.dotProduct_mulVec_le_of_le
      (sandwich_inv hEhatPd hM0pd
        (mul_pos hbeta (Real.sqrt_pos.mpr hkappa)) hup) x
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    exact h
  have hfac : 0 ≤ 2 * beta * (Real.sqrt kappa + 1) := by positivity
  have hstep : 2 * (x ⬝ᵥ M0 *ᵥ x) + 2 * (x ⬝ᵥ (Ehat * M0⁻¹ * Ehat) *ᵥ x) ≤
      2 * beta * (Real.sqrt kappa + 1) * (x ⬝ᵥ Ehat *ᵥ x) := by
    linarith only [hterm₁, hterm₂]
  have hfinal := mul_le_mul_of_nonneg_left hx hfac
  linarith only [hsplit, hstep, hfinal]

/-! ## The earlier-scale row loads -/

/-- The two block coordinate projections of a center have `𝐌₀`-energies adding
up to the full one, because `𝐌₀` is block diagonal. -/
theorem metric_split (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) (P Q : Vec d) :
    Sum.elim P (0 : Vec d) ⬝ᵥ M0 *ᵥ Sum.elim P 0 +
        Sum.elim (0 : Vec d) Q ⬝ᵥ M0 *ᵥ Sum.elim 0 Q =
      Sum.elim P Q ⬝ᵥ M0 *ᵥ Sum.elim P Q := by
  rw [hM0, quadratic_fromBlocks_diag, quadratic_fromBlocks_diag,
    quadratic_fromBlocks_diag]
  simp

/-- **The earlier-scale row load** `𝒬_s^± ≤ 8c_ε β√κ_s(√κ_t + 1)√θ`
(, proof).  The bound carried in the last
hypothesis is the center bound of `metric_center_le`. -/
theorem row_load_le {Eshat : FullBlockMat d}
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) {ceps kappaS bound : ℝ}
    (hc : 0 ≤ ceps * Real.sqrt kappaS)
    (hEs : Eshat ≤ (ceps * Real.sqrt kappaS) • M0) {P Q : Vec d}
    (hY : Sum.elim P Q ⬝ᵥ M0 *ᵥ Sum.elim P Q ≤ bound) :
    Sum.elim P (0 : Vec d) ⬝ᵥ Eshat *ᵥ Sum.elim P 0 +
        Sum.elim (0 : Vec d) Q ⬝ᵥ Eshat *ᵥ Sum.elim 0 Q ≤
      ceps * Real.sqrt kappaS * bound := by
  have h₁ := Initialization.dotProduct_mulVec_le_of_le hEs (Sum.elim P (0 : Vec d))
  have h₂ := Initialization.dotProduct_mulVec_le_of_le hEs (Sum.elim (0 : Vec d) Q)
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h₁ h₂
  have hsplit := metric_split (M0 := M0) hM0 P Q
  have hscaled := mul_le_mul_of_nonneg_left hY hc
  have hsum : Sum.elim P (0 : Vec d) ⬝ᵥ Eshat *ᵥ Sum.elim P 0 +
      Sum.elim (0 : Vec d) Q ⬝ᵥ Eshat *ᵥ Sum.elim 0 Q ≤
      ceps * Real.sqrt kappaS * (Sum.elim P Q ⬝ᵥ M0 *ᵥ Sum.elim P Q) := by
    rw [← hsplit, mul_add]
    linarith only [h₁, h₂]
  linarith only [hsum, hscaled]

end

end Response
end HighContrast
end Homogenization
