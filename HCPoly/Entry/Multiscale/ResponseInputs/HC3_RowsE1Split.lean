import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsOscSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsPartitionCell

/-!
# The cutoff-fluctuation average splits on the adapted cell

The cutoff estimate `e.response.cutoff.estimate` bounds the normalized average over the terminal
cell `HighContrast.adaptedCell q t` of the pairing `(φ - 1) * g`.  The two terms of that bound have
different natures: the oscillation of the cutoff inside a scale-`s` subcell is estimated pathwise,
whereas the departure of the subcell values from a common level is only controlled after taking
expectations.  This file records the exact algebraic identity that separates them.

The terminal average is first written as the flat average of the normalized averages over the
`3^{nd}` triadic subcells `adaptedCellAtCenter q (t - n) w` by `volumeAverage_adaptedCell_eq_flat_average`.
Each subcell term is then split at the level `⨍_{cell} φ - 1` of its own cutoff average by
`volumeAverage_weight_mul_split`: the fluctuation part `(φ - ⨍_{cell} φ) * g` carries the
within-cell oscillation, and the cell part `(⨍_{cell} φ - 1) * ⨍_{cell} g` carries the subcell
cutoff values.  Distributing the flat mean over the two parts gives the stated decomposition.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Splitting the cutoff-fluctuation average over the adapted cell**
(`e.response.cutoff.estimate`).  Let `q` be an invertible grid, `t` a generation, `n` a depth and
`φ`, `g` functions on the terminal cell `HighContrast.adaptedCell q t`, with `(φ - 1) * g` integrable
there.  Assume that on every depth-`n` triadic subcell `adaptedCellAtCenter q (t - n) w` the two summands
of the split of `(φ - 1) * g` at the level `⨍_{cell} φ - 1` are integrable, namely the fluctuation
`(φ - ⨍_{cell} φ) * g` and the level term `(⨍_{cell} φ - 1) * g`.  Then the terminal average of
`(φ - 1) * g` is the flat average over the subcells of the within-cell oscillation
`⨍_{cell} (φ - ⨍_{cell} φ) * g` plus the flat average over the subcells of the cell part
`(⨍_{cell} φ - 1) * ⨍_{cell} g`.  The identity is purely algebraic and needs no positivity of
either function. -/
theorem volumeAverage_fluct_eq_osc_add_cell {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) (φ g : Vec d → ℝ)
    (hint : IntegrableOn (fun x => (φ x - 1) * g x) (HighContrast.adaptedCell q t))
    (h1 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
      (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) * g x)
      (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * g x)
      = ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
        + ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g := by
  rw [volumeAverage_adaptedCell_eq_flat_average q hq t n (fun x => (φ x - 1) * g x) hint]
  have hsum : ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => (φ x - 1) * g x)
      = ∑ w ∈ triadicIndexBox d n,
          (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
            + (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g) := by
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hf : (fun x =>
          ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
        = (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x) := by
      funext x
      ring
    have havg : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x =>
            ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
        = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x) := by
      rw [hf]
    have hint1 : IntegrableOn
        (fun x =>
          ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
      rw [hf]
      exact h1 w hw
    calc volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => (φ x - 1) * g x)
        = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x =>
                ((φ x - 1) - (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1)) * g x)
            + (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g :=
          volumeAverage_weight_mul_split (fun x => φ x - 1)
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) g hint1 (h2 w hw)
      _ = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) * g x)
            + (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) g := by
          rw [havg]
  rw [hsum, Finset.sum_add_distrib, mul_add]

end

end Homogenization.HighContrast.Multiscale
