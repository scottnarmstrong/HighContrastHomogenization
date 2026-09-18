/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup

/-!
# Unit range of dependence

The local sigma-fields of two Borel sets at sup-distance at least one are
independent under the law.  The coefficient fields are uniformly elliptic almost
everywhere, with ellipticity constants belonging to the field and entering no
estimate; `e.qualitative.ellipticity` follows from this, and every
quantitative object of the development — `Π`, the gauge and its growth witness,
`Θ_m`, and every dimensional constant — is independent of them.
-/

/-- **Unit range of dependence.**  Local sigma-fields of unit-separated
Borel sets are independent. -/
def HCPoly.Frozen.IsUnitRangeLaw {d : ℕ}
    (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)) : Prop :=
  ∀ U V : Set (Homogenization.Vec d), MeasurableSet U → MeasurableSet V →
    Homogenization.HighContrast.UnitSeparated U V →
      ProbabilityTheory.Indep (Homogenization.HighContrast.coeffSigma d U)
        (Homogenization.HighContrast.coeffSigma d V) P

/-! ## The assumption under the project namespace

`Homogenization.HighContrast.IsUnitRangeLaw` is `HCPoly.Frozen.IsUnitRangeLaw` itself, not a second
reading of it: the proofs of the paper's propositions are written in the project
namespace and use the frozen declaration through this name. -/
namespace Homogenization.HighContrast

export HCPoly.Frozen (IsUnitRangeLaw)

end Homogenization.HighContrast
