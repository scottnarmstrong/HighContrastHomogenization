import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsE1Split
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The cutoff-mean defect splits coordinatewise on the adapted cell

The cutoff-mean defect of `e.response.cutoff.estimate` is, in each coordinate of each slot, the
`(φ - 1)`-weighted average of the optimizer state `X = (∇v, b ∇v)`
(`cutoffStateMeanAux_fst_sub`, `cutoffStateMeanAux_snd_sub`).  The cell decomposition of
`volumeAverage_fluct_eq_osc_add_cell` then splits that average over the depth-`n` triadic
subcells into a within-cell oscillation part of size `3^{-n}` and a cell part that cancels
after expectation.  This is the state-valued analogue of the split already landed for the
energy.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Coordinatewise split of the first cutoff-mean defect** (`e.response.cutoff.estimate`).
For an invertible grid `q`, a generation `t`, a depth `n` and a cutoff `φ`, the first-coordinate
cutoff-mean defect at the load coordinate `i`, namely `(cutoffStateMeanAux U φ b v).1 i` minus
the plain cell average `(cellAverage U (optimizerField b v)).1 i`, equals the flat average over
the depth-`n` triadic subcells of the within-cell oscillation
`⨍_{cell} (φ - ⨍_{cell} φ) * (X).1 i` plus the flat average of the cell part
`(⨍_{cell} φ - 1) * ⨍_{cell} (X).1 i`.  The identity is purely algebraic: it needs only the
integrability of the cutoff-weighted coordinate, of the coordinate itself, and of the two
summands of the split on every subcell. -/
theorem cutoffStateMeanAux_fst_eq_osc_add_cell {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) (φ : Vec d → ℝ) {b : CoeffField d}
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t)) (i : Fin d)
    (hφG : IntegrableOn (fun x => φ x * (optimizerField b v x).1 i) (HighContrast.adaptedCell q t))
    (hG : IntegrableOn (fun x => (optimizerField b v x).1 i) (HighContrast.adaptedCell q t))
    (hint : IntegrableOn (fun x => (φ x - 1) * (optimizerField b v x).1 i)
      (HighContrast.adaptedCell q t))
    (h1 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
        (optimizerField b v x).1 i) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
        (optimizerField b v x).1 i) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).1 i
        - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).1 i
      = ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
                (optimizerField b v x).1 i)
        + ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (fun x => (optimizerField b v x).1 i) := by
  have hsub : (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).1 i
      - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).1 i
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * (optimizerField b v x).1 i) := by
    simp only [cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_sub hφG hG]
    refine congrArg (volumeAverage (HighContrast.adaptedCell q t)) ?_
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  exact volumeAverage_fluct_eq_osc_add_cell q hq t n φ
    (fun x => (optimizerField b v x).1 i) hint h1 h2

/-- **Coordinatewise split of the second cutoff-mean defect** (`e.response.cutoff.estimate`).
For an invertible grid `q`, a generation `t`, a depth `n` and a cutoff `φ`, the second-coordinate
cutoff-mean defect at the flux coordinate `i`, namely `(cutoffStateMeanAux U φ b v).2 i` minus
the plain cell average `(cellAverage U (optimizerField b v)).2 i`, equals the flat average over
the depth-`n` triadic subcells of the within-cell oscillation
`⨍_{cell} (φ - ⨍_{cell} φ) * (X).2 i` plus the flat average of the cell part
`(⨍_{cell} φ - 1) * ⨍_{cell} (X).2 i`.  The identity is purely algebraic: it needs only the
integrability of the cutoff-weighted coordinate, of the coordinate itself, and of the two
summands of the split on every subcell. -/
theorem cutoffStateMeanAux_snd_eq_osc_add_cell {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) (φ : Vec d → ℝ) {b : CoeffField d}
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t)) (i : Fin d)
    (hφG : IntegrableOn (fun x => φ x * (optimizerField b v x).2 i) (HighContrast.adaptedCell q t))
    (hG : IntegrableOn (fun x => (optimizerField b v x).2 i) (HighContrast.adaptedCell q t))
    (hint : IntegrableOn (fun x => (φ x - 1) * (optimizerField b v x).2 i)
      (HighContrast.adaptedCell q t))
    (h1 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
        (optimizerField b v x).2 i) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2 : ∀ w ∈ triadicIndexBox d n, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
        (optimizerField b v x).2 i) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).2 i
        - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).2 i
      = ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ) *
                (optimizerField b v x).2 i)
        + ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (fun x => (optimizerField b v x).2 i) := by
  have hsub : (cutoffStateMeanAux (HighContrast.adaptedCell q t) φ b v).2 i
      - (cellAverage (HighContrast.adaptedCell q t) (optimizerField b v)).2 i
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * (optimizerField b v x).2 i) := by
    simp only [cutoffStateMeanAux, cellAverage]
    rw [← volumeAverage_sub hφG hG]
    refine congrArg (volumeAverage (HighContrast.adaptedCell q t)) ?_
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  exact volumeAverage_fluct_eq_osc_add_cell q hq t n φ
    (fun x => (optimizerField b v x).2 i) hint h1 h2

end

end Homogenization.HighContrast.Multiscale
