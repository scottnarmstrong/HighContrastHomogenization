import HCPoly.Entry.Geometry.QuadraticForm
import Mathlib.Analysis.Matrix.Order

/-!
# The positive square root `𝔪^{1/2}`

The print's `𝔪^{1/2}` for a positive matrix `𝔪` is Mathlib's `CFC.sqrt 𝔪`, the positive
semidefinite square root from the continuous functional calculus (`Mathlib.Analysis.Matrix.Order`
sets this up on real matrices under `open scoped MatrixOrder`).

What `e.rounded.grid.bounds` needs about it is the two eigenvalue statements of the print,
"the unrounded matrix `|𝔪⁻¹|^{1/2} 𝔪^{1/2}` has smallest eigenvalue one and largest eigenvalue
`(|𝔪| |𝔪⁻¹|)^{1/2}`", in the form of two-sided bounds on the quadratic form of `𝔪^{1/2}`:

* `⟨v, 𝔪^{1/2} v⟩ ≤ |𝔪|^{1/2} |v|²`, and
* `|v|² ≤ |𝔪⁻¹|^{1/2} ⟨v, 𝔪^{1/2} v⟩`.

Both are proved without the spectral theorem: the first from `|𝔪^{1/2} v|² = ⟨v, 𝔪 v⟩`, the second
by the same argument applied to `(𝔪^{1/2})⁻¹`, whose square is `𝔪⁻¹`, together with
Cauchy–Schwarz for the positive form of `(𝔪^{1/2})⁻¹`.
-/

namespace Homogenization.HighContrast.Geometry

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ} {m : Mat d}

theorem posDef_sqrt (hm : Matrix.PosDef m) : Matrix.PosDef (CFC.sqrt m) :=
  (Matrix.isStrictlyPositive_iff_posDef.mpr hm).sqrt.posDef

theorem sqrt_mul_sqrt (hm : Matrix.PosDef m) : CFC.sqrt m * CFC.sqrt m = m :=
  CFC.sqrt_mul_sqrt_self m hm.posSemidef.nonneg

theorem transpose_sqrt (hm : Matrix.PosDef m) : (CFC.sqrt m)ᵀ = CFC.sqrt m :=
  transpose_eq_of_isHermitian (posDef_sqrt hm).posSemidef.isHermitian

theorem sqrt_apply_comm (hm : Matrix.PosDef m) (a b : Fin d) :
    CFC.sqrt m b a = CFC.sqrt m a b := by
  have h := congrFun (congrFun (transpose_sqrt hm) a) b
  rwa [transpose_apply] at h

theorem dotProduct_sqrt_nonneg (hm : Matrix.PosDef m) (v : Vec d) :
    0 ≤ v ⬝ᵥ (CFC.sqrt m *ᵥ v) :=
  dotProduct_mulVec_nonneg_of_posSemidef (posDef_sqrt hm).posSemidef v

/-- The largest eigenvalue of `𝔪^{1/2}` is at most `|𝔪|^{1/2}`: `⟨v, 𝔪^{1/2} v⟩ ≤ √‖𝔪‖ |v|²`. -/
theorem dotProduct_sqrt_le (hm : Matrix.PosDef m) (v : Vec d) :
    v ⬝ᵥ (CFC.sqrt m *ᵥ v) ≤ Real.sqrt ‖m‖ * vecNormSq v :=
  dotProduct_mulVec_le_sqrt_opNorm_sq (transpose_sqrt hm) (sqrt_mul_sqrt hm) v

/-- The smallest eigenvalue of `𝔪^{1/2}` is at least `|𝔪⁻¹|^{-1/2}`:
`|v|² ≤ √‖𝔪⁻¹‖ ⟨v, 𝔪^{1/2} v⟩`. -/
theorem vecNormSq_le_sqrt_opNorm_inv_mul_dotProduct_sqrt (hm : Matrix.PosDef m) (v : Vec d) :
    vecNormSq v ≤ Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (CFC.sqrt m *ᵥ v)) := by
  set S := CFC.sqrt m with hSdef
  set R := S⁻¹ with hRdef
  have hS : Matrix.PosDef S := posDef_sqrt hm
  have hR : Matrix.PosDef R := hS.inv
  have hRt : Rᵀ = R := transpose_eq_of_isHermitian hR.posSemidef.isHermitian
  have hRpos : ∀ x : Vec d, 0 ≤ x ⬝ᵥ (R *ᵥ x) :=
    dotProduct_mulVec_nonneg_of_posSemidef hR.posSemidef
  have hRR : R * R = m⁻¹ := by
    rw [hRdef, ← Matrix.mul_inv_rev, hSdef, sqrt_mul_sqrt hm]
  have hRS : R * S = 1 :=
    Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit)
  have hRb : ∀ u : Vec d, u ⬝ᵥ (R *ᵥ u) ≤ Real.sqrt ‖m⁻¹‖ * vecNormSq u :=
    dotProduct_mulVec_le_sqrt_opNorm_sq hRt hRR
  have hRw : R *ᵥ (S *ᵥ v) = v := by
    rw [mulVec_mulVec, hRS, one_mulVec]
  have hvSv : v ⬝ᵥ (S *ᵥ v) = (S *ᵥ v) ⬝ᵥ (R *ᵥ (S *ᵥ v)) := by
    calc v ⬝ᵥ (S *ᵥ v) = (R *ᵥ (S *ᵥ v)) ⬝ᵥ (S *ᵥ v) := by rw [hRw]
      _ = (S *ᵥ v) ⬝ᵥ (R *ᵥ (S *ᵥ v)) := dotProduct_comm _ _
  have hcs := sq_dotProduct_mulVec_le hRt hRpos (S *ᵥ v) (R *ᵥ (S *ᵥ v))
  have h1 : (S *ᵥ v) ⬝ᵥ (R *ᵥ (R *ᵥ (S *ᵥ v))) = vecNormSq v := by
    conv_rhs => rw [← hRw]
    rw [vecNormSq_mulVec_eq hRt, mulVec_mulVec]
  have h2 : (R *ᵥ (S *ᵥ v)) ⬝ᵥ (R *ᵥ (R *ᵥ (S *ᵥ v))) ≤ Real.sqrt ‖m⁻¹‖ * vecNormSq v := by
    rw [hRw]
    exact hRb v
  rw [h1] at hcs
  have hv := vecNormSq_nonneg v
  have hS0 : 0 ≤ v ⬝ᵥ (S *ᵥ v) := dotProduct_sqrt_nonneg hm v
  have hN := Real.sqrt_nonneg ‖m⁻¹‖
  rcases eq_or_lt_of_le hv with h0 | h0
  · rw [← h0]
    exact mul_nonneg hN hS0
  · have h3 : vecNormSq v * vecNormSq v
        ≤ (Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (S *ᵥ v))) * vecNormSq v := by
      calc vecNormSq v * vecNormSq v = vecNormSq v ^ 2 := by ring
        _ ≤ ((S *ᵥ v) ⬝ᵥ (R *ᵥ (S *ᵥ v))) * ((R *ᵥ (S *ᵥ v)) ⬝ᵥ (R *ᵥ (R *ᵥ (S *ᵥ v)))) :=
            hcs
        _ ≤ (v ⬝ᵥ (S *ᵥ v)) * (Real.sqrt ‖m⁻¹‖ * vecNormSq v) := by
            rw [hvSv]
            exact mul_le_mul_of_nonneg_left h2 (hRpos _)
        _ = (Real.sqrt ‖m⁻¹‖ * (v ⬝ᵥ (S *ᵥ v))) * vecNormSq v := by ring
    exact le_of_mul_le_mul_right h3 h0

end Homogenization.HighContrast.Geometry
