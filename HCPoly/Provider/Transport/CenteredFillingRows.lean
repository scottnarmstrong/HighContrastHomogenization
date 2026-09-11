/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredRowAveraging
import HCPoly.Provider.Recurrence.SchattenIdeal

/-!
# The centered rows of the filling at the terminal normalization

The centered part of the principal cell sum is measured at the *terminal*
normalization `E_t^q`, not at the normalization of the source scale, and the
change of normalization to the terminal generation says what that costs: the
congruence between the two normalizations is paid by the operator norm of the
relative mean, which the determinant bounds control by `e^{Δ_{r,t}^q}`.

This file carries that step down to the single cell and then assembles the two
halves of the printed estimate.  The single-cell statement is the entrywise form
the averaging lemma consumes: an aligned scale-`r` cell is an integer translate
of the cell at the origin, so by stationarity of the coefficient law its
normalized centered entries have the `L^Q` norm of the cell at the origin, which
the Schatten ideal property bounds by `e^{Δ_{r,t}^q}` times the centered moment
`v_r^q`.  The assembled statement is the square-weight bounds for the boundary
and bulk cells in the form the transport uses them:
the mixed norm of the centered matrix sum of the filling, at the terminal
normalization, is at most a constant times

`Σ_r (Σ_{V ∈ 𝒱_r} (|V|/|W|)²)^{1/2} e^{Δ_{r,t}^q} v_r^q`.

The `ℓ²` weight is written in the exact form of `sqrt_sum_sq_const`: on a
filling row all the weights are the same real number, so the sum of squares is
that number squared times the number of cells, and no weighted generalization of
`l.fixed.geometry.matrix.averaging` is involved anywhere.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The sharp normalization at one cell -/

/-- **The change of normalization to the terminal generation, entrywise at one
aligned cell.**  The normalized centered entries of an aligned scale-`r` cell,
measured at the terminal normalization `E_t^q`, have `L^Q` norm at most
`(2d)^{1/Q}e^{Δ_{r,t}^q}` times the centered moment `v_r^q`.

Two steps: stationarity of the coefficient law moves the cell to the origin, and
the ideal property of the Schatten size exchanges the two normalizations at the
cost of the determinant increment.  The dimensional factor is the one the ideal
property carries; the printed display states the estimate for the Schatten size
itself,
where it is sharp. -/
theorem lqNorm_adaptedCellAt_le_transported_centeredMoment {P : Measure (CoeffSpace d)}
    (hPs : HCPoly.Frozen.IsStationaryLaw P) {Q : ℝ} (hQ : 0 < Q) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {r t : ℤ} (hlr : l ≤ r)
    (hEr : Book.Ch02.BlockPosDef (adaptedMean P q r))
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (hmean : BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q r))
    (w : Fin d → ℤ) (α β : BlockCoord d) :
    lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q r w) a) (adaptedMean P q r))
        (adaptedMean P q t)) α β) ≤
      ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) *
        centeredMoment P Q q r := by
  have hsymr : IsSymmetricBlockMat (adaptedMean P q r) := Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hsymt : IsSymmetricBlockMat (adaptedMean P q t) := Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hEr' : (toFullBlockMat (adaptedMean P q r)).PosDef := posDef_toFullBlockMat hsymr hEr
  have hEt' : (toFullBlockMat (adaptedMean P q t)).PosDef := posDef_toFullBlockMat hsymt hEt
  have hmean' : toFullBlockMat (adaptedMean P q t) ≤ toFullBlockMat (adaptedMean P q r) :=
    le_of_blockMatLoewnerLE hsymt hsymr hmean
  have hcell : ∀ a : CoeffSpace d, IsSymmetricBlockMat
      (blockSub (coarseBlock (adaptedCell q r) a) (adaptedMean P q r)) := fun a =>
    Recurrence.isSymmetricBlockMat_coarseBlock_sub a hsymr
  rw [Recurrence.lqNorm_normalizedBlock_adaptedCellAt_eq hPs hq hlr (adaptedMean P q r)
    (adaptedMean P q t) w α β]
  refine le_trans (Recurrence.lqNorm_normalizedBlock_le_lqSchattenSize P hQ hcell
    (adaptedMean P q t) α β) ?_
  exact Recurrence.lqSchattenSize_le_of_le hEr' hEt' hmean' hcell hQ

/-! ## The centered matrix sum of the filling -/

/-- **The centered matrix sum of the filling at the terminal normalization.**
The rows of the maximal filling are aligned families of one scale, so all the
weights of a row agree; the finite-range averaging lemma pays each row by its
`ℓ²` weight, and the sharp normalization pays the passage from the source
normalization to the terminal one.  The result is the printed estimate

`‖Σ_r Σ_V (|V|/|W|)(𝐀(V) - E_r^q)‖_{L^Q(S_Q)} ≤ C Σ_r (Σ_V (|V|/|W|)²)^{1/2}
   e^{Δ_{r,t}^q} v_r^q`,

with `C = 2d(2Q + 4C_{RB}√Q)√(3^d)` and the dimensional factor `(2d)^{1/Q}` of
the ideal property inside the row coefficient.  The `ℓ²` weight is displayed in
the exact constant-row form: on a row of constant weight `c r` it is
`(Σ_{V ∈ 𝒱_r} (c r)²)^{1/2}`. -/
theorem centered_filling_rows_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hPs : HCPoly.Frozen.IsStationaryLaw P) (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ}
    (hQ : 2 ≤ Q) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {t : ℤ}
    {R : Finset ℤ} {Z : ℤ → Finset (Fin d → ℤ)} {c : ℤ → ℝ}
    (hc : ∀ r ∈ R, 0 ≤ c r) (hl : ∀ r ∈ R, l ≤ r)
    (hint : ∀ r ∈ R, HasFiniteAdaptedMean P q r)
    (hEr : ∀ r ∈ R, Book.Ch02.BlockPosDef (adaptedMean P q r))
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (hmean : ∀ r ∈ R, BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q r))
    (hfin : ∀ r ∈ R, centeredMoment P Q q r ≠ ⊤) :
    lqSchattenSize P Q (fun a => ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
        c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
          (adaptedMean P q r)))) (adaptedMean P q t) ≤
      ENNReal.ofReal (2 * (d : ℝ) *
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            Real.sqrt ((3 : ℝ) ^ d))) *
        ∑ r ∈ R, ENNReal.ofReal (Real.sqrt (∑ _w ∈ Z r, c r ^ 2) *
            ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (detIncrement P q r t))) *
          centeredMoment P Q q r := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  set v : ℤ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) *
      centeredMoment P Q q r with hvdef
  have hvtop : ∀ r ∈ R, v r ≠ ⊤ := by
    intro r hr
    rw [hvdef]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin r hr)
  have hbd : ∀ r ∈ R, ∀ w ∈ Z r, ∀ α β : BlockCoord d,
      lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q r w) a) (adaptedMean P q r))
        (adaptedMean P q t)) α β) ≤ v r := fun r hr w _ α β =>
    lqNorm_adaptedCellAt_le_transported_centeredMoment hPs hQ0 hq (hl r hr) (hEr r hr) hEt
      (hmean r hr) w α β
  refine le_trans (lqSchattenSize_filling_rows_le hPs hP hQ hq (adaptedMean P q t) hc hl hint
    hvtop hbd) ?_
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun r hr => ?_)
  have hseam : Real.sqrt (∑ _w ∈ Z r, c r ^ 2) = c r * Real.sqrt ((Z r).card : ℝ) :=
    sqrt_sum_sq_const (Z r) (hc r hr)
  rw [hvdef, hseam, ← mul_assoc,
    ENNReal.ofReal_mul (mul_nonneg (hc r hr) (Real.sqrt_nonneg _))]

end

end Transport
end HighContrast
end Homogenization
