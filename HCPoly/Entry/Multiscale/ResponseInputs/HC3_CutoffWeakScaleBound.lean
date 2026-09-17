import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSubcellFenchel
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage

/-!
# The pathwise per-scale bound for the weak-quantity integrand

The scale-average seminorm `[·]` of AK.HC (2.130) is built from the squared `L²` cell means of the
optimizer state on the depth-`n` triadic subcells of the response cell.  This file records the
pathwise bound those subcell terms satisfy: after the test block `S` and the shift `Y` are applied,
the normalized sum over the subcells is controlled by the pathwise symmetric energy of the
harmonic field on the response cell.  The estimate chains the cell-average half of the Fenchel
bound (2.15) on each subcell with the exact partition identity of the subcell energy averages.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise per-scale bound for the weak-quantity integrand `e.response.weak.estimate`: for a
`b`-harmonic field `v` on the response cell `U_t = adaptedCell q t`, a test block `S` with
`|S X|² ≤ kS |X|²`, a shift `Y`, and a constant `K` that bounds the coarse block of `b` augmented
by the swap block `𝐑` on every depth-`n` triadic subcell, the normalized sum over the `3 ^ (n d)`
subcells of the squared length of `S` applied to the shifted subcell average of the optimizer
field of `v` is at most `kS (2 K ⟨∇v ⬝ symm(b) ∇v⟩_{U_t} + 2 |Y|²)`.  The proof applies the
cell-average half of the Fenchel bound (2.15) on each subcell, averages the subcell energy over the
exact partition of `U_t`, and expands the shift; this is the pathwise input of the scale-average
seminorm bound AK.HC (2.130). -/
theorem avsum_optimizerState_sq_le_of_inputs {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (S : BlockMat d) (Y : BlockVec d) (kS : ℝ) (hkS : 0 ≤ kS)
    (hS : ∀ X : BlockVec d, blockVecDot (blockMatVecMul S X) (blockMatVecMul S X)
        ≤ kS * blockVecDot X X)
    (K : ℝ) (hK : 0 < K)
    (hB : ∀ w ∈ triadicIndexBox d n, ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul
        (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
          + toFullBlockMat (blockSwap d))) X) ≤ K * blockVecDot X X)
    (hint : IntegrableOn (scalarVariationEnergyIntegrand b v) (HighContrast.adaptedCell q t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
        blockVecDot
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
      ≤ kS * (2 * (K * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
              + 2 * blockVecDot Y Y) := by
  classical
  have hNpos : (0 : ℝ) < ((triadicIndexBox d n).card : ℝ) := by
    rw [card_triadicIndexBox n]
    positivity
  have hNne : ((triadicIndexBox d n).card : ℝ) ≠ 0 := ne_of_gt hNpos
  have hInvNN : (0 : ℝ) ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  -- The pointwise bound: `S` does not increase the squared length, and the shift is expanded.
  have hpt : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul S
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
          (blockMatVecMul S
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
        ≤ kS * (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y)) := by
    intro w _
    have h1 := hS (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y)
    have h2 := blockVecDot_sub_self_le
      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)) Y
    have h3 : kS * blockVecDot
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y)
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y)
        ≤ kS * (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y)) := by
      refine mul_le_mul_of_nonneg_left ?_ hkS
      linarith only [h2]
    linarith only [h1, h3]
  -- Fenchel on every subcell, then the exact partition average over the subcells.
  have hfen : (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
      ≤ K * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v) := by
    have hcell : ∀ w ∈ triadicIndexBox d n,
        blockVecDot
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
          ≤ K * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarVariationEnergyIntegrand b v) := by
      intro w hw
      exact blockVecDot_cellAverage_subcell_le (d := d) hq t n hw hEll v K hK (hB w hw)
    calc
      (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
          ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                K * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (scalarVariationEnergyIntegrand b v) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) hInvNN
      _ = K * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (scalarVariationEnergyIntegrand b v)) := by
            rw [← Finset.mul_sum]
            ring
      _ = K * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v) := by
            rw [avsum_volumeAverage_eq q hq t n hint]
  -- The normalized sum of the shifted squares.
  have hFk : (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          kS * (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
      = kS * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))) := by
    rw [← Finset.mul_sum]
    ring
  have hFshift : (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
      = 2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
        + 2 * blockVecDot Y Y := by
    have hsummand : ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
        = ∑ w ∈ triadicIndexBox d n,
          (2 * blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + 2 * blockVecDot Y Y) :=
      Finset.sum_congr rfl (fun w _ => by ring)
    have hsum_eval : ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
        = 2 * (∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
          + ((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y) := by
      rw [hsummand, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hc2 : (((triadicIndexBox d n).card : ℝ))⁻¹ *
          (((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y)) = 2 * blockVecDot Y Y := by
      calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
            (((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y))
          = ((((triadicIndexBox d n).card : ℝ))⁻¹ * ((triadicIndexBox d n).card : ℝ))
              * (2 * blockVecDot Y Y) := by ring
        _ = 1 * (2 * blockVecDot Y Y) := by rw [inv_mul_cancel₀ hNne]
        _ = 2 * blockVecDot Y Y := by ring
    calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            (2 * (blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              + blockVecDot Y Y))
        = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            (2 * (∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
              + ((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y)) := by
          rw [hsum_eval]
      _ = 2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
          + 2 * blockVecDot Y Y := by
          rw [mul_add, hc2]
          ring
  -- Assemble.
  calc
    (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
        blockVecDot
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
        ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              kS * (2 * (blockVecDot
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                + blockVecDot Y Y)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) hInvNN
    _ = kS * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            (2 * (blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              + blockVecDot Y Y))) := hFk
    _ = kS * (2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
          + 2 * blockVecDot Y Y) := by rw [hFshift]
    _ ≤ kS * (2 * (K * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v))
          + 2 * blockVecDot Y Y) := by
          refine mul_le_mul_of_nonneg_left ?_ hkS
          linarith only [hfen]

end

end Homogenization.HighContrast.Multiscale
