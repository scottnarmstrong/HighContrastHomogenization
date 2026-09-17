import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffWeakScaleBound
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffBesovScaleSum

/-!
# The pathwise seminorm bound by the cell energy

The scale-average seminorm `[·]` of AK.HC (2.130) is a sum of per-scale cell averages.  The
per-scale bound `avsum_optimizerState_sq_le_of_inputs` controls each scale by the pathwise cell
energy with a coarse-block envelope `K = K₀ · 3 ^ (ρ n)`, while the summation
`besovSeminorm_sq_le_of_scale_bound` accepts any per-scale majorant `A · 3 ^ (ρ n)` with `ρ < 1`.
This file chains the two: the envelope and the shift are monotone in the geometric factor
`3 ^ (ρ n) ≥ 1`, so the per-scale bound can be rewritten in the majorant shape with the geometric
loss absorbed into the coefficient `A`.  This is the pathwise input `e.response.weak.estimate`
into the squared scale-average seminorm bound AK.HC (2.130).
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise bound of the squared scale-average seminorm AK.HC (2.130) by the cell energy,
with the geometric loss absorbed.  For a `b`-harmonic field `v` on the response cell
`U_t = adaptedCell q t`, a test block `S` with `|S X|² ≤ kS |X|²`, a shift `Y`, and a coarse-block
envelope of the augmented block on every depth-`n` triadic subcell of the form
`K₀ · 3 ^ (ρ n)` with `ρ < 1`, the squared scale-average seminorm of the applied, shifted cell
averages of the optimizer field is at most `((1 - 3 ^ ((ρ - 1) / 2))⁻¹)²` times
`3 ^ t (kS (2 K₀ ⟨∇v ⬝ symm(b) ∇v⟩_{U_t} + 2 |Y|²))`.  The proof applies the per-scale pathwise
bound at envelope `K₀ · 3 ^ (ρ n)`, then uses `3 ^ (ρ n) ≥ 1` and the nonnegativity of the energy,
the shift and `kS` to move the geometric factor onto the whole per-scale majorant, so that the
scale-weighted summation `e.response.weak.estimate` of AK.HC (2.130) applies. -/
theorem besovSeminorm_sq_optimizerState_le_of_scale_bounds {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (S : BlockMat d) (Y : BlockVec d) (kS : ℝ) (hkS : 0 ≤ kS)
    (hS : ∀ X : BlockVec d, blockVecDot (blockMatVecMul S X) (blockMatVecMul S X)
        ≤ kS * blockVecDot X X)
    (K₀ : ℝ) (hK₀ : 0 < K₀)
    (hB : ∀ (n : ℕ), ∀ w ∈ triadicIndexBox d n, ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul
        (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
          + toFullBlockMat (blockSwap d))) X)
        ≤ (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))) * blockVecDot X X)
    (hint : IntegrableOn (scalarVariationEnergyIntegrand b v) (HighContrast.adaptedCell q t))
    (hEnn : 0 ≤ volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v)) :
    besovSeminorm t (fun n z => blockMatVecMul S
        (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) z) (optimizerField b v) - Y)) ^ 2
      ≤ ((1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 *
          ((3 : ℝ) ^ (t : ℝ) *
            (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
                  (scalarVariationEnergyIntegrand b v))
                + 2 * blockVecDot Y Y))) := by
  classical
  have hBnn : 0 ≤ blockVecDot Y Y := blockVecDot_nonneg Y
  have hE0 : 0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (scalarVariationEnergyIntegrand b v) := hEnn
  have hA0 : 0 ≤ kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
        (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y) := by
    refine mul_nonneg hkS (add_nonneg ?_ ?_)
    · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg (le_of_lt hK₀) hE0)
    · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBnn
  -- The per-scale majorant `A * 3 ^ (ρ * n)` with `A` the absorbed coefficient.
  have hper : ∀ n : ℕ,
      (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (blockMatVecMul S
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
              (blockMatVecMul S
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
        ≤ (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y))
            * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
    intro n
    have hp0le : (0 : ℝ) ≤ ρ * (n : ℝ) := mul_nonneg hρ0 (Nat.cast_nonneg n)
    have hp1 : (1 : ℝ) ≤ (3 : ℝ) ^ (ρ * (n : ℝ)) :=
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hp0le
    have hp0 : (0 : ℝ) < (3 : ℝ) ^ (ρ * (n : ℝ)) := lt_of_lt_of_le zero_lt_one hp1
    have hKpos : 0 < K₀ * (3 : ℝ) ^ (ρ * (n : ℝ)) := mul_pos hK₀ hp0
    have hbase := avsum_optimizerState_sq_le_of_inputs (d := d) hq t n hEll v S Y kS hkS hS
      (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))) hKpos (hB n) hint
    -- Absorb the geometric factor `3 ^ (ρ * n) ≥ 1` into the constant coefficient.
    have h2B : 2 * blockVecDot Y Y
        ≤ (2 * blockVecDot Y Y) * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
      simpa using mul_le_mul_of_nonneg_left hp1
        (show (0 : ℝ) ≤ 2 * blockVecDot Y Y by linarith only [hBnn])
    have hstep : 2 * (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))
            * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
          + 2 * blockVecDot Y Y
        ≤ (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
      have hKterm : 2 * (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))
            * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
          = (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
                (scalarVariationEnergyIntegrand b v))) * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
        ring
      have hsplit : (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ))
          = (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
                (scalarVariationEnergyIntegrand b v))) * (3 : ℝ) ^ (ρ * (n : ℝ))
            + (2 * blockVecDot Y Y) * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
        ring
      rw [hKterm, hsplit]
      exact add_le_add (le_refl _) h2B
    have hle1 : kS * (2 * (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))
            * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
          + 2 * blockVecDot Y Y)
        ≤ kS * ((2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hstep hkS
    have hle2 : kS * ((2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ)))
        = (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y))
            * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
      ring
    rw [hle2] at hle1
    exact le_trans hbase hle1
  exact besovSeminorm_sq_le_of_scale_bound t ρ
    (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
          (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y))
    hρ1 hρ0 hA0
    (fun n z => blockMatVecMul S
      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) z) (optimizerField b v) - Y))
    hper

end

end Homogenization.HighContrast.Multiscale
