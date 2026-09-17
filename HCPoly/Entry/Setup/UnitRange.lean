import HCPoly.Setup.LocalSigmaFields
import HCPoly.Setup.CoefficientSpace

/-!
# The unit-range assumption

The local sigma-fields of two Borel sets at sup-distance at least one are independent under
the law.  The coefficient fields are locally uniformly elliptic in the qualitative sense, with
ellipticity constants belonging to the field and entering no estimate; every quantitative
object of the development — `Π`, the gauge and its growth witness, `Θ_m`, and every
dimensional constant — is independent of them.

The name and signature reproduce those of the older `highcontrast-poly` development.
-/

open Homogenization.HighContrast (CoeffSpace UnitSeparated coeffSigma)
namespace Homogenization.HighContrast

/-- **The unit-range assumption.**  Local sigma-fields of unit-separated Borel sets are
independent. -/
def IsUnitRangeLaw {d : ℕ} (P : MeasureTheory.Measure (CoeffSpace d)) : Prop :=
  ∀ U V : Set (Vec d), MeasurableSet U → MeasurableSet V → UnitSeparated U V →
    ProbabilityTheory.Indep (coeffSigma d U) (coeffSigma d V) P

end Homogenization.HighContrast
