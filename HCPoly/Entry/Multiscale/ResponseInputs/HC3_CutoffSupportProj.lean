import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The defining properties of the response cutoff class

`IsResponseCutoff qq t φ` is the class of cutoffs used by the cutoff estimate
`e.response.cutoff.estimate`: a function supported in the adapted cell `HighContrast.adaptedCell qq t`,
bounded between `0` and `2`, of volume average one there, and carrying the first- and
second-derivative bounds at the scale `3 ^ t` in `qq`-coordinates.  Each defining property is
exposed here as a named theorem, so that consumers can refer to a property by name rather than by
a positional projection.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` is nonnegative
everywhere. -/
theorem IsResponseCutoff.nonneg {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (x : Vec d) : 0 ≤ φ x :=
  h.1 x

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` is bounded above
by `2` everywhere. -/
theorem IsResponseCutoff.le_two {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (x : Vec d) : φ x ≤ 2 :=
  h.2.1 x

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` vanishes at every
point outside the adapted cell `HighContrast.adaptedCell qq t`. -/
theorem IsResponseCutoff.zero_of_notMem {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : ∀ x, x ∉ HighContrast.adaptedCell qq t → φ x = 0 :=
  h.2.2.1

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` has volume
average one on the adapted cell `HighContrast.adaptedCell qq t`. -/
theorem IsResponseCutoff.volumeAverage_eq_one {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) :
    volumeAverage (HighContrast.adaptedCell qq t) φ = 1 :=
  h.2.2.2.1

/-- The pullback `y ↦ φ (qq y)` of a cutoff `φ` of the class of the cutoff estimate
`e.response.cutoff.estimate` is Lipschitz with constant
`32 * d ^ 2 * responseCutoffProfileConst * 3 ^ (-t)`. -/
theorem IsResponseCutoff.lipschitz {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) :
    LipschitzWith
      (Real.toNNReal
        (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)))
      (fun y : Vec d => φ (matVecMul qq y)) :=
  h.2.2.2.2.1

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` is smooth, i.e.
`C^∞`. -/
theorem IsResponseCutoff.contDiff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : ContDiff ℝ (⊤ : ℕ∞) φ :=
  h.2.2.2.2.2.1

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` has compact
support. -/
theorem IsResponseCutoff.hasCompactSupport {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : HasCompactSupport φ :=
  h.2.2.2.2.2.2.1

/-- The topological support of a cutoff `φ` of the class of the cutoff estimate
`e.response.cutoff.estimate` is contained in the adapted cell `HighContrast.adaptedCell qq t`. -/
theorem IsResponseCutoff.tsupport_subset {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : tsupport φ ⊆ HighContrast.adaptedCell qq t :=
  h.2.2.2.2.2.2.2.1

end

end Homogenization.HighContrast.Multiscale
