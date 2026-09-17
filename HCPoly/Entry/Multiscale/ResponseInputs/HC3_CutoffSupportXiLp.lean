import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportXi
import Homogenization.Multiscale.NormalizedNorms
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Data.ENNReal.Real

/-!
# Bounded weight fields are `L^∞` for the normalized cube measure

The negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)) pairs the cutoff weight field `ξ` against
a centred potential in the normalized pairing on a cube.  Its hypothesis on `ξ` is uniform
boundedness, `‖ξ y‖ ≤ K` for every `y`.  The two declarations below show that such a field is
`L^∞` for `normalizedCubeMeasure Q`, with `L^∞` norm at most `K`, so that the duality bound can
consume the weight field directly.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- A vector field bounded uniformly by `K` is essentially bounded, hence `L^∞`, for the
normalized cube measure (`AK.HC` Lemma A.1, (A.4)). -/
theorem memLp_top_normalizedCubeMeasure_of_norm_le {d : ℕ} (Q : TriadicCube d)
    {ξ : Vec d → Vec d} (hξm : MeasureTheory.AEStronglyMeasurable ξ (normalizedCubeMeasure Q))
    {K : ℝ} (hK : ∀ y, ‖ξ y‖ ≤ K) :
    MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q) :=
  MeasureTheory.memLp_top_of_bound hξm K (Filter.Eventually.of_forall hK)

/-- The normalized `L^∞` norm of a vector field bounded uniformly by `K` is at most `K`
(`AK.HC` Lemma A.1, (A.4)). -/
theorem cubeLpNorm_top_le_of_norm_le {d : ℕ} (Q : TriadicCube d)
    {ξ : Vec d → Vec d} {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ y, ‖ξ y‖ ≤ K) :
    cubeLpNorm Q ∞ ξ ≤ K := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal hK0
    (MeasureTheory.eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hK))

end

end Homogenization.HighContrast.Multiscale
