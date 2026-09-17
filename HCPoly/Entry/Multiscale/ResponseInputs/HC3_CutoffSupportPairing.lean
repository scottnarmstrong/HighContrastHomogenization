import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportBesov
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The cutoff-weighted pairing bound on a cell

This file records the crude Cauchy--Schwarz bound for a cutoff-weighted pairing of two
square-integrable vector fields on a cell, used in the cutoff argument of
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)).  If `φ` is a cutoff with `0 ≤ φ ≤ 2`,
`A` and `B` are vector fields and `vol` denotes the normalized cell average, then

`|vol (φ · (A · B))| ≤ 2 · √(vol |A|²) · √(vol |B|²)`.

The three ingredients are the pointwise Cauchy--Schwarz inequality for the Euclidean dot
product, the monotonicity of the normalized cell average under pointwise domination, and an
averaged Cauchy--Schwarz (Hölder with conjugate exponents `2` and `2`) for nonnegative
functions.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Monotonicity of the normalized cell average: if `|f| ≤ g` pointwise on the measurable set
`U` and both are integrable on `U`, then `|vol f| ≤ vol g`.  The prefactor `(vol U)⁻¹` is
nonnegative and the set integral is monotone.  This is the averaging step of the
cutoff-weighted pairing bound `e.response.cutoff.estimate`. -/
theorem volumeAverage_abs_le_of_le {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hU : MeasurableSet U) (hle : ∀ x ∈ U, |f x| ≤ g x)
    (hf : MeasureTheory.IntegrableOn f U) (hg : MeasureTheory.IntegrableOn g U) :
    |volumeAverage U f| ≤ volumeAverage U g := by
  unfold volumeAverage
  have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  calc |∫ x in U, f x| ≤ ∫ x in U, |f x| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x in U, g x := MeasureTheory.setIntegral_mono_on hf.abs hg hU hle

end

end Homogenization.HighContrast.Multiscale
