import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ENNReal.Holder

/-!
# Integrability of the cutoff integrands of the pathwise expansion of `p.response.transfer`

The pathwise expansion of the cutoff pairing in the cutoff estimate of `p.response.transfer`
needs six scalar integrands to be integrable on the terminal cell.  All six are products of the
bounded cutoff `φ` with either a coordinate of the doubled optimizer state `X = (∇v, b ∇v)`, a
coordinate pairing of `X` with a constant vector, or the pairing `X₁·X₂`.  On a set of finite
volume, with both slots of `X` square integrable and `0 ≤ φ ≤ 2`, the bounded-measurable-factor
lemma gives the first three, and the `L² × L² → L¹` Hölder pairing gives the last.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A measurable function bounded by `Mφ` in absolute value, multiplied by an integrable
function, is integrable on any set.  The pointwise bound `|φ x| ≤ Mφ` supplies the
almost-everywhere norm bound required by `Integrable.bdd_mul`. -/
theorem integrableOn_cutoff_mul_coord {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (hUfin : volume U ≠ ⊤) {φ : Vec d → ℝ} (hφm : Measurable φ) {Mφ : ℝ}
    (hφb : ∀ x, |φ x| ≤ Mφ) {g : Vec d → ℝ} (hg : IntegrableOn g U) :
    IntegrableOn (fun x => φ x * g x) U := by
  have hU_used : MeasurableSet U := hU
  have hUfin_used : volume U ≠ ⊤ := hUfin
  exact Integrable.bdd_mul hg hφm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact hφb x)

end

end Homogenization.HighContrast.Multiscale
