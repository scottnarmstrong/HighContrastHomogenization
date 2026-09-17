import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Measurability of the scale-average seminorm

The scale-average seminorm `besovSeminorm` is a countable sum whose summands are built from the
sample-dependent cell averages of a doubled field. This file records that such a sum is a
measurable function of the sample whenever its summands are, and applies this to
`besovSeminorm`.

The only point requiring care is that the real `tsum` is defined by a junk value `0` where the
series is not summable; the summability set is nevertheless measurable, because for real series it
agrees with the boundedness of the partial sums of the absolute values.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Filter

noncomputable section

variable {d : ℕ}

/-- A pointwise countable sum of measurable real-valued functions is measurable. No summability
hypothesis is needed: the series is summable on a measurable set, where the real `tsum` is the
limit of the partial sums, and takes the junk value `0` off that set. -/
theorem measurable_tsum_of_measurable {α : Type*} [MeasurableSpace α] {g : ℕ → α → ℝ}
    (hg : ∀ n, Measurable (g n)) : Measurable fun a => ∑' n, g n a := by
  classical
  have hpart : ∀ N : ℕ, Measurable fun a => ∑ n ∈ Finset.range N, g n a :=
    fun N => Finset.measurable_sum (Finset.range N) fun n _ => hg n
  have hbdd : MeasurableSet
      {a | BddAbove (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, |g n a|)} :=
    measurableSet_bddAbove_range fun N =>
      Finset.measurable_sum (Finset.range N) fun n _ => by
        simpa only [Real.norm_eq_abs] using (hg n).norm
  have hset : {a | Summable fun n => g n a} =
      {a | BddAbove (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, |g n a|)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨∑' n, |g n a|,
        fun x ⟨N, hN⟩ => hN ▸ Summable.sum_le_tsum (Finset.range N)
          (fun n _ => abs_nonneg _) h.abs⟩
    · intro h
      obtain ⟨C, hC⟩ := h
      exact Summable.of_abs
        (summable_of_sum_range_le (fun n => abs_nonneg _) fun N => hC (Set.mem_range_self N))
  have hsum : MeasurableSet {a | Summable fun n => g n a} := by
    rw [hset]
    exact hbdd
  have hfun : (fun a => if Summable fun n => g n a then
        liminf (fun N => ∑ n ∈ Finset.range N, g n a) atTop else (0 : ℝ)) =
      fun a => ∑' n, g n a := by
    funext a
    by_cases ha : Summable fun n => g n a
    · rw [if_pos ha]
      exact ((Summable.hasSum ha).tendsto_sum_nat).liminf_eq
    · rw [if_neg ha, tsum_eq_zero_of_not_summable ha]
  rw [← hfun]
  exact Measurable.ite hsum (Measurable.liminf hpart) measurable_const

/-- The scale-average seminorm `besovSeminorm` of AK.HC (2.130) is a measurable function of the
sample. Each summand is a constant times the square root of a finite sum of products of the
coordinates of the sample-dependent cell averages, hence measurable; the countable sum is
measurable by `measurable_tsum_of_measurable`. -/
theorem measurable_besovSeminorm {α : Type*} [MeasurableSpace α] (t : ℤ)
    {avg : α → ℕ → (Fin d → ℤ) → BlockVec d}
    (h1 : ∀ n w i, Measurable fun a => (avg a n w).1 i)
    (h2 : ∀ n w i, Measurable fun a => (avg a n w).2 i) :
    Measurable fun a => besovSeminorm t (avg a) := by
  refine measurable_tsum_of_measurable fun n => ?_
  have hinner : Measurable fun a =>
      ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg a n w) (avg a n w) := by
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum (triadicIndexBox d n) fun w _ => ?_
    simp only [blockVecDot, vecDot]
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum Finset.univ fun i _ => ?_
      exact (h1 n w i).mul (h1 n w i)
    · refine Finset.measurable_sum Finset.univ fun i _ => ?_
      exact (h2 n w i).mul (h2 n w i)
  exact hinner.sqrt.const_mul _

end

end Homogenization.HighContrast.Multiscale
