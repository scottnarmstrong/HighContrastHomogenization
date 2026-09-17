import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# Integrability of the doubled optimizer field on a subcell

Every cell-average step of the diagonal weak-norm estimate moves a matrix through the cell
average of the doubled optimizer field `optimizerField b u = (∇v, b ∇v)`, so each such step
needs both slots of that field to be integrable on the cell.

The gradient slot is `L²` because it is the weak gradient of an `H¹` function, and `L²` of a
finite measure is `L¹`.  The flux slot is `L²` because a uniformly elliptic coefficient field is
essentially bounded on the set where it is elliptic, and the product of a bounded measurable
field with an `L²` gradient is again `L²`.

The ellipticity hypothesis on the flux slot cannot be dropped.  For instance on `(0,1)` take
`∇v ≡ 1` (an `L²` gradient) and the measurable but unbounded scalar field `b x = x⁻¹`: then the
gradient slot is `L²` while the flux `b ∇v = x⁻¹` is not `L¹`.  So a bound on the coefficient
field is exactly what makes the flux slot integrable.

The gradient is `L²` only on the domain `U` to which the `AHarmonicFunction` is attached, so
these statements are asked on subsets `V ⊆ U`.  In the estimate the relevant subsets are the
triadic subcells `adaptedCellAtCenter q (t - n) w` of `HighContrast.adaptedCell q t`, which is why the box
version below carries the membership `w ∈ triadicIndexBox d n`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The gradient slot of the doubled optimizer field is integrable on every finite-measure
subset of the domain: `H1Function.gradMemL2` gives `L²`, and `L² ⊆ L¹` there. -/
theorem h6a_integrableOn_optimizerField_fst_pub {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hVfin : volume V ≠ ⊤) (b : CoeffField d) (u : AHarmonicFunction b U) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField b u x).1 j) V := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have h2 : MemLp (fun x => u.toH1.grad x j) 2 (volume.restrict U) := u.toH1.gradMemL2 j
  have h2' : MemLp (fun x => u.toH1.grad x j) 2 (volume.restrict V) :=
    h2.mono_measure (Measure.restrict_mono hVU le_rfl)
  exact MemLp.integrable (by norm_num) h2'

end

end Homogenization.HighContrast.Multiscale
