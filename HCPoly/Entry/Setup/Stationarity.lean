import HCPoly.Setup.LocalSigmaFields
import HCPoly.Setup.CoefficientSpace

/-!
# The stationarity assumption

The law of the coefficient field is invariant under the integer translations of the
coefficient space.  The coefficient fields are locally uniformly elliptic in the qualitative
sense, with ellipticity constants belonging to the field and entering no estimate; every
quantitative object of the development — `Π`, the gauge and its growth witness, `Θ_m`, and
every dimensional constant — is independent of them.

The name and signature reproduce those of the older `highcontrast-poly` development.
-/

open Homogenization.HighContrast (CoeffSpace translateCoeff)
namespace Homogenization.HighContrast

/-- **The stationarity assumption.**  Every integer translation of the coefficient space
preserves the law. -/
def IsStationaryLaw {d : ℕ} (P : MeasureTheory.Measure (CoeffSpace d)) : Prop :=
  ∀ z : Fin d → ℤ, MeasureTheory.Measure.map (translateCoeff z) P = P

end Homogenization.HighContrast
