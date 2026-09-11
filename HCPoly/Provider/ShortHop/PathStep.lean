/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.MatrixPower
import HCPoly.Setup.TransportObjects

/-!
# The candidate of the short test

The candidate witness of `p.successful.short.bridge` is the next point
on the fixed constant-speed projective path from the current witness to the
canonical metric of the old grid's terminal block: the path point at parameter
`min{c_hop/d_pr, 1}`, and the endpoint itself when the two projective classes
already agree.  Two of the three candidate clauses of the proposition are proved
here — the candidate is a positive witness, and the projective jump to it is at
most the hop length.  The third, the bound on the cross-grid factor, is the hop
distortion read at those two facts.

The path point `m(θ) = m₀^{1/2}(m₀^{-1/2}m₁m₀^{-1/2})^θm₀^{1/2}` is a congruence
of the real power of the normalized pair, so normalizing it by `m₀^{-1/2}` gives
back that real power exactly.  Positive definiteness is then the positive
definiteness of the real power carried across the congruence, and the printed
form of the projective distance — half the sum of the logarithms of the sizes of
the normalized pair and of its inverse — turns the constant-speed bound into the
two size bounds of the real power.  This is where the path is *constant speed*:
each of the two logarithms is multiplied by `θ`, so the distance is at most `θ`
times the distance to the endpoint.

The zero branch costs nothing: the candidate is the endpoint, and the distance to
it is the vanishing distance itself.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The path point as a congruence -/

/-- **Normalizing the path point returns the real power.**  The path point is the
congruence of `(m₀^{-1/2}m₁m₀^{-1/2})^θ` by `m₀^{1/2}`, and conjugating back by
`m₀^{-1/2}` undoes it. -/
theorem normalize_projPath {m0 m1 : Mat d} (h0 : m0.PosDef) (theta : ℝ) :
    matSqrt m0⁻¹ * projPath m0 m1 theta * matSqrt m0⁻¹ =
      matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) := by
  have hu : IsUnit (matSqrt m0).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt h0)
  have hleft : matSqrt m0⁻¹ * matSqrt m0 = 1 := by
    rw [matSqrt_inv h0]; exact Matrix.nonsing_inv_mul _ hu
  have hright : matSqrt m0 * matSqrt m0⁻¹ = 1 := by
    rw [matSqrt_inv h0]; exact Matrix.mul_nonsing_inv _ hu
  calc matSqrt m0⁻¹ * projPath m0 m1 theta * matSqrt m0⁻¹
      = matSqrt m0⁻¹ * matSqrt m0 *
          matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) *
          (matSqrt m0 * matSqrt m0⁻¹) := by
        simp only [projPath]; noncomm_ring
    _ = matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) := by
        rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]

/-- **The real power of a positive definite matrix is positive definite**, in the
carrier of the transport layer. -/
theorem posDef_matPow [Nonempty (Fin d)] {A : Mat d} (hA : A.PosDef) {theta : ℝ}
    (htheta : 0 ≤ theta) : (matPow theta A).PosDef :=
  posDef_cfc_rpow hA htheta

/-- **The path point is a positive witness.** -/
theorem posDef_projPath [Nonempty (Fin d)] {m0 m1 : Mat d} (h0 : m0.PosDef)
    (h1 : m1.PosDef) {theta : ℝ} (htheta : 0 ≤ theta) : (projPath m0 m1 theta).PosDef := by
  have hY : (matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹)).PosDef :=
    posDef_matPow (posDef_normalize h1 h0) htheta
  have hS : (matSqrt m0)ᴴ = matSqrt m0 := (matSqrt_spec h0.posSemidef).1.isHermitian
  have hcong := posDef_conj hY (isUnit_matSqrt h0)
  rw [hS] at hcong
  exact hcong

/-! ## The constant-speed bound -/

/-- **The path has constant speed.**  The projective distance from the base point
to the path point at parameter `θ` is at most `θ` times the distance to the
endpoint. -/
theorem projDist_projPath_le [Nonempty (Fin d)] {m0 m1 : Mat d} (h0 : m0.PosDef)
    (h1 : m1.PosDef) {theta : ℝ} (htheta : 0 ≤ theta) :
    projDist m0 (projPath m0 m1 theta) ≤ theta * projDist m0 m1 := by
  have hX : (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹).PosDef := posDef_normalize h1 h0
  have hY : (matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹)).PosDef :=
    posDef_matPow hX htheta
  rw [projDist_eq_norm_form h0 (posDef_projPath h0 h1 htheta),
    projDist_eq_norm_form h0 h1, normalize_projPath h0 theta]
  have hup : ‖matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹)‖ ≤
      ‖matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹‖ ^ theta := norm_cfc_rpow_le hX htheta
  have hlo : ‖(matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹))⁻¹‖ ≤
      ‖(matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹)⁻¹‖ ^ theta := norm_inv_cfc_rpow_le hX htheta
  have hlog1 : Real.log ‖matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹)‖ ≤
      theta * Real.log ‖matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹‖ := by
    have hstep := Real.log_le_log (norm_pos_of_posDef hY) hup
    rwa [Real.log_rpow (norm_pos_of_posDef hX)] at hstep
  have hlog2 : Real.log ‖(matPow theta (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹))⁻¹‖ ≤
      theta * Real.log ‖(matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹)⁻¹‖ := by
    have hstep := Real.log_le_log (norm_pos_of_posDef hY.inv) hlo
    rwa [Real.log_rpow (norm_pos_of_posDef hX.inv)] at hstep
  linarith only [hlog1, hlog2]

/-! ## The candidate -/

/-- **The candidate is a positive witness.** -/
theorem posDef_projPathStep [Nonempty (Fin d)] {c : ℝ} (hc : 0 ≤ c) {m0 m1 : Mat d}
    (h0 : m0.PosDef) (h1 : m1.PosDef) : (projPathStep c m0 m1).PosDef := by
  simp only [projPathStep]
  split_ifs with hz
  · exact h1
  · have hD : 0 < projDist m0 m1 := lt_of_le_of_ne (projDist_nonneg h0 h1) (Ne.symm hz)
    exact posDef_projPath h0 h1 (le_min (div_nonneg hc hD.le) zero_le_one)

/-- **The candidate is within one hop length.** -/
theorem projDist_projPathStep_le [Nonempty (Fin d)] {c : ℝ} (hc : 0 ≤ c) {m0 m1 : Mat d}
    (h0 : m0.PosDef) (h1 : m1.PosDef) : projDist m0 (projPathStep c m0 m1) ≤ c := by
  simp only [projPathStep]
  split_ifs with hz
  · rw [hz]; exact hc
  · have hD : 0 < projDist m0 m1 := lt_of_le_of_ne (projDist_nonneg h0 h1) (Ne.symm hz)
    have hstep := projDist_projPath_le h0 h1 (le_min (div_nonneg hc hD.le) zero_le_one)
    have hbound : min (c / projDist m0 m1) 1 * projDist m0 m1 ≤ c := by
      have h := mul_le_mul_of_nonneg_right (min_le_left (c / projDist m0 m1) 1) hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at h
    linarith only [hstep, hbound]

/-- The canonical metric of a positive definite doubled block is a positive
witness. -/
theorem posDef_canonicalMetric {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) :
    (canonicalMetric E).PosDef := posDef_canonMetric hE

/-- **The two candidate clauses of the short test.**  The next point on the fixed
path from the current witness to the canonical metric of the terminal block is a
positive witness at projective distance at most the hop length. -/
theorem candidate_of_short_test [Nonempty (Fin d)] {chop : ℝ} (hchop : 0 ≤ chop)
    {mu : Mat d} (hmu : mu.PosDef) {Et : BlockMat d}
    (hEt : (toFullBlockMat Et).PosDef) {mu' : Mat d}
    (hmu' : mu' = projPathStep chop mu (canonicalMetric Et)) :
    mu'.PosDef ∧ projDist mu mu' ≤ chop := by
  subst hmu'
  exact ⟨posDef_projPathStep hchop hmu (posDef_canonicalMetric hEt),
    projDist_projPathStep_le hchop hmu (posDef_canonicalMetric hEt)⟩

end

end ShortHop
end HighContrast
end Homogenization
