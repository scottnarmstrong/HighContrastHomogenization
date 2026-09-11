/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup

/-!
# Stationarity of the coefficient law

The law of the coefficient field is invariant under the integer translations of
the coefficient space.  The coefficient fields are uniformly elliptic almost
everywhere, with ellipticity constants belonging to the field and entering no
estimate; `e.qualitative.ellipticity` follows from this, and every
quantitative object of the development — `Π`, the gauge and its growth witness,
`Θ_m`, and every dimensional constant — is independent of them.
-/

/-- **Stationarity of the coefficient law.**  Every integer translation of the
coefficient space preserves the law. -/
def HCPoly.Frozen.IsStationaryLaw {d : ℕ}
    (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)) : Prop :=
  ∀ z : Fin d → ℤ,
    MeasureTheory.Measure.map (Homogenization.HighContrast.translateCoeff z) P = P
