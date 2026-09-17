import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffEnergyDefect
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The competitor split of the weighted optimizer energy

The first error row of the cutoff estimate of `p.response.transfer` replaces the terminal
optimizer energy of a cell by the scale-`s` cell optimizers.  The pathwise algebra behind that
replacement is the identity

`∇v · b ∇v − ∇w · b ∇w = (∇v − ∇w) · symmPart b (∇v + ∇w)`,

which holds because the quadratic form only sees the symmetric part of `b`.  Combined with the
Cauchy–Schwarz inequality for the positive semidefinite symmetric part, it bounds the
`(φ − 1)`-weighted energy defect of two competitors by the square roots of the averaged
difference and sum energies.

* `abs_vecDot_matVecMul_le_sqrt_mul_sqrt` — Cauchy–Schwarz for a symmetric positive
  semidefinite matrix.
* the pathwise competitor identity for the optimizer field.
* the weighted energy defect bound.

Paper: the first error row of `p.response.transfer`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Cauchy–Schwarz for a symmetric positive semidefinite matrix.**  For a real matrix `S` with
`matTranspose S = S` whose quadratic form is nonnegative, the pairing `u · S w` is bounded by the
square roots of the two diagonal energies `u · S u` and `w · S w`, i.e.
`|u · S w| ≤ √(u · S u) · √(w · S w)`. -/
theorem abs_vecDot_matVecMul_le_sqrt_mul_sqrt {d : ℕ} {S : Mat d}
    (hsymm : matTranspose S = S) (hpsd : ∀ z : Vec d, 0 ≤ vecDot z (matVecMul S z))
    (u w : Vec d) :
    |vecDot u (matVecMul S w)|
      ≤ Real.sqrt (vecDot u (matVecMul S u)) * Real.sqrt (vecDot w (matVecMul S w)) := by
  have hsymm' : S.IsSymm := by
    change matTranspose S = S
    exact hsymm
  have hsq : vecDot u (matVecMul S w) ^ 2
      ≤ vecDot u (matVecMul S u) * vecDot w (matVecMul S w) :=
    sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hsymm' hpsd u w
  calc |vecDot u (matVecMul S w)|
      = Real.sqrt (vecDot u (matVecMul S w) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecDot u (matVecMul S u) * vecDot w (matVecMul S w)) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (vecDot u (matVecMul S u)) * Real.sqrt (vecDot w (matVecMul S w)) :=
        Real.sqrt_mul (hpsd u) _

end

end Homogenization.HighContrast.Multiscale
