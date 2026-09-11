/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.RoundedCenteredCoeffSpace
import Homogenization.Book.Ch03.Definitions

/-!
# Chapter 3 family for the rounded centered coefficient

The R3-A coefficient is first constructed on the almost-everywhere quotient
carrier.  This module packages that same quotient representative as one
compatible Chapter 3 coefficient family and records its almost-everywhere
identification with the literal rounded field.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Every qualitative coefficient sample has a compatible Chapter 3 family
whose representative is unchanged on every reference cube. -/
theorem exists_coeffFamily_of_coeffSpace (a : CoeffSpace d) :
    ∃ aRef : Book.Ch03.CoeffFamily d,
      ∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField = (⇑a.1 : CoeffField d) := by
  classical
  have hdata : ∀ Q : TriadicCube d, ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volume, x ∈ openCubeSet Q →
        IsEllipticMatrix lam Lam ((⇑a.1 : CoeffField d) x) := fun Q =>
    a.2.exists_ae_isEllipticMatrix_of_isBounded (isBounded_openCubeSet Q)
  let aRef : Book.Ch03.CoeffFamily d :=
    { coeffOn := fun Q ↦
        { toCoeffField := ⇑a.1
          lam := (hdata Q).choose
          Lam := (hdata Q).choose_spec.choose
          lam_pos := (hdata Q).choose_spec.choose_spec.1
          lam_le_Lam := (hdata Q).choose_spec.choose_spec.2.1
          aeStronglyMeasurable := by
            intro i j
            have hentry : AEStronglyMeasurable
                (fun x : Vec d ↦ (⇑a.1 : CoeffField d) x i j) volume :=
              (continuous_id.matrix_elem i j).comp_aestronglyMeasurable
                a.1.aestronglyMeasurable
            refine hentry.restrict.congr ?_
            filter_upwards [ae_restrict_mem
              (Book.Ch02.cubeDomain Q).measurableSet] with x hx
            change x ∈ openCubeSet Q at hx
            simp [restrictCoeffField, hx]
          aeElliptic := by
            filter_upwards
              [ae_restrict_of_ae (hdata Q).choose_spec.choose_spec.2.2,
                ae_restrict_mem (Book.Ch02.cubeDomain Q).measurableSet]
              with x hx hxQ
            exact hx hxQ }
      restrictsTo_of_subset := by
        intro Q R _hRQ
        exact Filter.EventuallyEq.rfl }
  exact ⟨aRef, fun Q ↦ rfl⟩

end

end HighContrast
end Homogenization
