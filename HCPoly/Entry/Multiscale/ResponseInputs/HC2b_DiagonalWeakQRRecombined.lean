import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakQuadraticResponse

/-!
# Quadratic response recombined over the cells

On a single child cell `V` of a parent `U`, the variation energy of the
difference between the parent field and the cell maximizer equals twice the
response deficit of the parent field on that cell
(`h6a_difference_energy_eq_response_deficit`).  The present file averages that
identity over the finitely many cells of a partition and uses
`h6a_average_over_partition` to turn the flat average of the per-cell parent
integrands into the parent average.  When the parent field is itself the
maximizer on `U`, `responseJ_eq_of_isResponseMaximizer` identifies that parent
average with `ResponseJ U p q a`, so the flat average of the cell difference
energies equals twice the difference between the flat average of the cell
responses and the parent response.

The per-cell average of the parent integrand depends on the cell, so the abstract
recombination below carries `gavg : iota → ℝ`, not a single constant.  A constant
`gavg` would be correct only when every cell has the same parent integrand,
which the partition step does not provide, and it would not typecheck against
`h6a_average_over_partition`, whose right-hand side is the parent average.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **Averaging a per-cell deficit identity over a finite index set.**  Suppose
the cells are indexed by the nonempty finite set `Z`, each cell carries the
deficit identity `Eng w = 2 (Jchild w − gavg w)` for its own parent average
`gavg w`, and the flat average of those parent averages is `Jparent`.  Then the
flat average of `Eng` is twice the difference between the flat average of
`Jchild` and `Jparent`.  The index set is required nonempty only so that the
inverse cardinality behaves; the statement is an identity in the sums. -/
theorem h6a_avg_difference_energy_eq_deficit {iota : Type*} (Z : Finset iota)
    (Eng Jchild gavg : iota → ℝ) (Jparent : ℝ)
    (hZ : Z.Nonempty)
    (hpair : ∀ w ∈ Z, Eng w = 2 * (Jchild w - gavg w))
    (hrecomb : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, gavg w = Jparent) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Eng w
      = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Jchild w - Jparent) := by
  have hEng : ∑ w ∈ Z, Eng w = 2 * (∑ w ∈ Z, Jchild w - ∑ w ∈ Z, gavg w) := by
    rw [Finset.sum_congr rfl (fun w hw => hpair w hw), ← Finset.mul_sum,
      Finset.sum_sub_distrib]
  have hcard : (Z.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hZ)
  have hrecomb' : Jparent * (Z.card : ℝ) = ∑ w ∈ Z, gavg w := by
    rw [← hrecomb, mul_right_comm, inv_mul_cancel₀ hcard, one_mul]
  have hP : Jparent = (∑ w ∈ Z, gavg w) * (Z.card : ℝ)⁻¹ := by
    calc Jparent = (Jparent * (Z.card : ℝ)) * (Z.card : ℝ)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hcard, mul_one]
      _ = (∑ w ∈ Z, gavg w) * (Z.card : ℝ)⁻¹ := by rw [hrecomb']
  rw [hEng, hP]
  ring

end

end Homogenization.HighContrast.Multiscale
