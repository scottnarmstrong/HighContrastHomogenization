import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Integrability of one nonnegative term of an integrable sum

The first error row of `p.response.transfer` needs the `P`-integrability of each subcell deficit
and of each subcell energy separately, while the exact partition identity supplies only the
integrability of their flat average.  Both families are nonnegative, so each member is dominated
by the whole sum; with almost-everywhere strong measurability of the member, integrability
follows.  This file records that elementary principle in the two forms the row consumes: a sum
bounded above by an integrable function, and a sum equal to one.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

/-- **A single nonnegative term of a sum bounded by an integrable function is integrable.**  Let
`f i` be nonnegative for every `i ∈ Z`, let each `f i` be `P`-a.e.-strongly measurable, let `g`
be `P`-integrable, and suppose `∑ i ∈ Z, f i a ≤ g a` for every `a`.  Then each `f i` with
`i ∈ Z` is `P`-integrable.  At every point the fixed term is bounded by the full sum through the
nonnegativity of the other terms and the sum is bounded by `g`; the norm in the domination
criterion is the term itself because the term is nonnegative. -/
theorem integrable_of_nonneg_of_sum_le {α ι : Type*} [MeasurableSpace α] {P : Measure α}
    {Z : Finset ι} {f : ι → α → ℝ} {g : α → ℝ}
    (hf0 : ∀ i ∈ Z, ∀ a, 0 ≤ f i a)
    (hmeas : ∀ i ∈ Z, MeasureTheory.AEStronglyMeasurable (f i) P)
    (hg : MeasureTheory.Integrable g P)
    (hsum : ∀ a, ∑ i ∈ Z, f i a ≤ g a) :
    ∀ i ∈ Z, MeasureTheory.Integrable (f i) P := by
  intro i hi
  refine hg.mono' (hmeas i hi) ?_
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 i hi a)]
  exact (Finset.single_le_sum (fun j hj => hf0 j hj a) hi).trans (hsum a)

/-- **A single nonnegative term of a sum equal to an integrable function is integrable.**  This
is the previous statement with the upper bound `∑ i ∈ Z, f i a ≤ g a` strengthened to the
identity `∑ i ∈ Z, f i a = g a` supplied by the exact partition identity of
`p.response.transfer`; the identity gives the bound by `le_of_eq`. -/
theorem integrable_of_nonneg_of_sum_eq {α ι : Type*} [MeasurableSpace α] {P : Measure α}
    {Z : Finset ι} {f : ι → α → ℝ} {g : α → ℝ}
    (hf0 : ∀ i ∈ Z, ∀ a, 0 ≤ f i a)
    (hmeas : ∀ i ∈ Z, MeasureTheory.AEStronglyMeasurable (f i) P)
    (hg : MeasureTheory.Integrable g P)
    (hsum : ∀ a, ∑ i ∈ Z, f i a = g a) :
    ∀ i ∈ Z, MeasureTheory.Integrable (f i) P :=
  integrable_of_nonneg_of_sum_le hf0 hmeas hg fun a => le_of_eq (hsum a)

end Homogenization.HighContrast.Multiscale
