/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.DeterminantLoss
import HCPoly.Geometry.GeometricMeanToolkit
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The real power of a positive definite matrix

The constant-speed projective path of `e.renormalization.geometry.update` reads the
real power `A^θ` of a positive definite matrix, taken by the continuous
functional calculus.  Two facts about it are needed: it is again positive
definite, and its size and the size of its inverse are the corresponding sizes
of `A` raised to the power `θ`.

Both come from the same squeeze.  On positive definite data the spectrum lies in
the interval `[|A^{-1}|^{-1}, |A|]`: the upper end is the statement that the
spectral norm is the largest eigenvalue, read through the functional calculus,
and the lower end is that statement applied to the inverse and turned around.
Raising the squeeze to the power `θ ≥ 0` bounds the spectrum of `A^θ` inside
`[(|A^{-1}|^θ)^{-1}, |A|^θ]`, and the two Loewner comparisons against multiples
of the identity that this produces give the positive definiteness and the two
size bounds at once.

Only the two inequalities are proved, not the identities `|A^θ| = |A|^θ` and
`|A^{-θ}| = |A^{-1}|^θ`, because only the inequalities are used: the path bound
of the short hop is an upper bound on a projective distance, and each of its two
logarithms is bounded above by one of these.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Positivity of the spectral size -/

/-- A positive definite matrix has positive spectral size. -/
theorem norm_pos_of_posDef [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef) : 0 < ‖X‖ :=
  norm_pos_iff.mpr hX.isUnit.ne_zero

/-! ## The spectrum of a positive definite matrix -/

/-- **The spectrum is below the spectral size.** -/
theorem spectrum_le_norm {X : Matrix n n ℝ} (hX : X.PosDef) {x : ℝ}
    (hx : x ∈ spectrum ℝ X) : x ≤ ‖X‖ := by
  have h : X ≤ ‖X‖ • (1 : Matrix n n ℝ) := le_norm_smul_one hX.posSemidef
  rw [← Algebra.algebraMap_eq_smul_one] at h
  exact (le_algebraMap_iff_spectrum_le (a := X) hX.isHermitian.isSelfAdjoint).mp h x hx

/-- **The spectrum is above the reciprocal of the spectral size of the
inverse.** -/
theorem inv_norm_inv_le_spectrum [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef) {x : ℝ}
    (hx : x ∈ spectrum ℝ X) : ‖X⁻¹‖⁻¹ ≤ x := by
  have hnpos : 0 < ‖X⁻¹‖ := norm_pos_of_posDef hX.inv
  have hone : IsUnit (1 : Matrix n n ℝ).det := by simp
  have hinvle : X⁻¹ ≤ ‖X⁻¹‖ • (1 : Matrix n n ℝ) := le_norm_smul_one hX.inv.posSemidef
  have hstep := inv_le_inv_of_le hX.inv (posDef_smul Matrix.PosDef.one hnpos) hinvle
  rw [inv_smul_of_isUnit hnpos.ne' hone, inv_one,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hX),
    ← Algebra.algebraMap_eq_smul_one] at hstep
  exact (algebraMap_le_iff_le_spectrum (a := X) hX.isHermitian.isSelfAdjoint).mp hstep x hx

/-- The real power is continuous on the spectrum of a positive definite
matrix. -/
private theorem continuousOn_rpow_spectrum [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef)
    (theta : ℝ) : ContinuousOn (fun x : ℝ => x ^ theta) (spectrum ℝ X) := fun x hx =>
  (Real.continuousAt_rpow_const x theta
      (Or.inl (lt_of_lt_of_le (inv_pos.mpr (norm_pos_of_posDef hX.inv))
        (inv_norm_inv_le_spectrum hX hx)).ne')).continuousWithinAt

/-! ## The two Loewner comparisons for the real power -/

/-- **The real power is below the corresponding power of the spectral size.** -/
theorem cfc_rpow_le_smul_one [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef) {theta : ℝ}
    (htheta : 0 ≤ theta) :
    cfc (fun x : ℝ => x ^ theta) X ≤ (‖X‖ ^ theta) • (1 : Matrix n n ℝ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  refine (cfc_le_algebraMap_iff (fun x : ℝ => x ^ theta) (‖X‖ ^ theta) X
    (continuousOn_rpow_spectrum hX theta) hX.isHermitian.isSelfAdjoint).mpr fun x hx => ?_
  have hx0 : (0 : ℝ) ≤ x :=
    le_trans (inv_nonneg.mpr (norm_nonneg _)) (inv_norm_inv_le_spectrum hX hx)
  exact Real.rpow_le_rpow hx0 (spectrum_le_norm hX hx) htheta

/-- **The real power is above the reciprocal of the corresponding power of the
spectral size of the inverse.** -/
theorem smul_one_le_cfc_rpow [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef) {theta : ℝ}
    (htheta : 0 ≤ theta) :
    ((‖X⁻¹‖ ^ theta)⁻¹) • (1 : Matrix n n ℝ) ≤ cfc (fun x : ℝ => x ^ theta) X := by
  rw [← Algebra.algebraMap_eq_smul_one]
  refine (algebraMap_le_cfc_iff (fun x : ℝ => x ^ theta) ((‖X⁻¹‖ ^ theta)⁻¹) X
    (continuousOn_rpow_spectrum hX theta) hX.isHermitian.isSelfAdjoint).mpr fun x hx => ?_
  have hstep := Real.rpow_le_rpow (inv_nonneg.mpr (norm_nonneg (X⁻¹)))
    (inv_norm_inv_le_spectrum hX hx) htheta
  rwa [Real.inv_rpow (norm_nonneg _)] at hstep

/-! ## Positive definiteness and the two size bounds -/

/-- **The real power of a positive definite matrix is positive definite.** -/
theorem posDef_cfc_rpow [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef) {theta : ℝ}
    (htheta : 0 ≤ theta) : (cfc (fun x : ℝ => x ^ theta) X).PosDef := by
  have hpos : (0 : ℝ) < (‖X⁻¹‖ ^ theta)⁻¹ :=
    inv_pos.mpr (Real.rpow_pos_of_pos (norm_pos_of_posDef hX.inv) theta)
  exact posDef_of_posDef_le (posDef_smul Matrix.PosDef.one hpos)
    (smul_one_le_cfc_rpow hX htheta)

/-- **The size of the real power.** -/
theorem norm_cfc_rpow_le [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef) {theta : ℝ}
    (htheta : 0 ≤ theta) : ‖cfc (fun x : ℝ => x ^ theta) X‖ ≤ ‖X‖ ^ theta :=
  norm_le_of_le_smul_one (posDef_cfc_rpow hX htheta).posSemidef
    (Real.rpow_nonneg (norm_nonneg X) theta) (cfc_rpow_le_smul_one hX htheta)

/-- **The size of the inverse of the real power.** -/
theorem norm_inv_cfc_rpow_le [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosDef) {theta : ℝ}
    (htheta : 0 ≤ theta) :
    ‖(cfc (fun x : ℝ => x ^ theta) X)⁻¹‖ ≤ ‖X⁻¹‖ ^ theta := by
  have hpow : (0 : ℝ) < ‖X⁻¹‖ ^ theta :=
    Real.rpow_pos_of_pos (norm_pos_of_posDef hX.inv) theta
  have hone : IsUnit (1 : Matrix n n ℝ).det := by simp
  have hY : (cfc (fun x : ℝ => x ^ theta) X).PosDef := posDef_cfc_rpow hX htheta
  have hstep := inv_le_inv_of_le (posDef_smul Matrix.PosDef.one (inv_pos.mpr hpow)) hY
    (smul_one_le_cfc_rpow hX htheta)
  rw [inv_smul_of_isUnit (inv_pos.mpr hpow).ne' hone, inv_one, inv_inv] at hstep
  exact norm_le_of_le_smul_one hY.inv.posSemidef hpow.le hstep

end

end ShortHop
end HighContrast
end Homogenization
