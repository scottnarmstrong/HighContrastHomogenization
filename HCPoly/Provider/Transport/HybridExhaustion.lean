/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridPartition
import HCPoly.Provider.Transport.FillingExhaustion

/-!
# Positive-limit reverse hybrid exhaustion

The hybrid residual has geometric decay with a cutoff-independent response
majorant.  Hence every common bound for the finite packed-and-selected sums
also bounds the outer target response, in both primal and sharp-adjoint form.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem le_of_forall_geometric {x T C : ℝ}
    (h : ∀ m : ℕ, x ≤ T + C * (1 / 3 : ℝ) ^ m) : x ≤ T := by
  have hlim : Filter.Tendsto (fun m : ℕ => T + C * (1 / 3 : ℝ) ^ m)
      Filter.atTop (nhds T) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
    simpa using (hpow.const_mul C).const_add T
  exact ge_of_tendsto' hlim h

private theorem hybrid_residual_ratio_le {q q' : Mat d} (hd : 2 ≤ d)
    (hq : q.PosDef) (hq' : q'.PosDef) {n l J : ℤ} (hJn : J ≤ n)
    (y : Vec d) :
    (volume (hybridStrip q' n (adaptedCellTranslate q (n + l) y) \
      ⋃ r ∈ Set.Icc J n, ⋃ w ∈ fillingIndex q n
        (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r,
          adaptedCellAt q r w)).toReal /
        (volume (adaptedCellTranslate q (n + l) y)).toReal ≤
      (2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d) *
            (2 * (d : ℝ) * Real.sqrt d) * 2 *
              (1 + 6 * Real.sqrt d) ^ (d - 1)) *
        gridRatio q q' * (3 : ℝ) ^ (J - (n + l)) := by
  have hWtop := volume_adaptedCellTranslate_ne_top q (n + l) y
  have hWpos : (0 : ℝ) <
      (volume (adaptedCellTranslate q (n + l) y)).toReal :=
    ENNReal.toReal_pos (volume_adaptedCellTranslate_ne_zero hq (n + l) y) hWtop
  have hC0 : 0 ≤
      (2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d) *
            (2 * (d : ℝ) * Real.sqrt d) * 2 *
              (1 + 6 * Real.sqrt d) ^ (d - 1)) *
        gridRatio q q' * (3 : ℝ) ^ (J - (n + l)) := by
    rw [gridRatio]
    positivity
  have hle := volume_hybridFilling_residual_le (l := l) hd hq hq' hJn y
  have hmono := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWtop) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at hmono
  exact (div_le_iff₀ hWpos).mpr hmono

/-- The positive-limit primal hybrid exhaustion. -/
theorem blockQuadratic_coarseBlock_le_of_forall_hybrid_rows [NeZero d]
    {q q' : Mat d} (hd : 2 ≤ d) (hq : q.PosDef) (hq' : q'.PosDef)
    {n l : ℤ} (y : Vec d) {Zp : Finset (Fin d → ℤ)}
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZp : ↑Zp = hybridPackingIndex q' n
      (adaptedCellTranslate q (n + l) y))
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r)
    (a : CoeffSpace d) (X : BlockVec d) {T : ℝ}
    (hT : ∀ J : ℤ, J ≤ n →
      (∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal /
          (volume (adaptedCellTranslate q (n + l) y)).toReal *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
        ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
          (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate q (n + l) y)).toReal *
              (1 / 2 * blockVecDot X
                (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X)) ≤ T) :
    1 / 2 * blockVecDot X
      (blockMatVecMul (coarseBlock (adaptedCellTranslate q (n + l) y) a) X) ≤ T := by
  obtain ⟨C, hC0, hfinite⟩ :=
    exists_blockQuadratic_coarseBlock_le_hybrid_rows hq hq' hZp hZ a X
  let R : ℝ := (2 * (d : ℝ) * Real.sqrt d +
      (2 * (d : ℝ) * Real.sqrt d) *
        (2 * (d : ℝ) * Real.sqrt d) * 2 *
          (1 + 6 * Real.sqrt d) ^ (d - 1)) *
      gridRatio q q' * (3 : ℝ) ^ (-l)
  refine le_of_forall_geometric (C := R * C) fun m => ?_
  refine (hfinite (n - (m : ℤ))).trans ?_
  have hres := hybrid_residual_ratio_le hd hq hq'
    (n := n) (J := n - (m : ℤ)) (l := l) (by omega) y
  have hrate :
      (2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d) *
            (2 * (d : ℝ) * Real.sqrt d) * 2 *
              (1 + 6 * Real.sqrt d) ^ (d - 1)) *
        gridRatio q q' * (3 : ℝ) ^ (n - (m : ℤ) - (n + l)) =
      R * (1 / 3 : ℝ) ^ m := by
    dsimp only [R]
    have hpow : (3 : ℝ) ^ (n - (m : ℤ) - (n + l)) =
        (3 : ℝ) ^ (-l) * (1 / 3 : ℝ) ^ m := by
      rw [show n - (m : ℤ) - (n + l) = -l + -(m : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, zpow_neg,
        one_div, inv_pow, zpow_natCast]
    rw [hpow]
    ring
  rw [hrate] at hres
  calc
    _ ≤ T +
        (volume (hybridStrip q' n (adaptedCellTranslate q (n + l) y) \
          ⋃ r ∈ Set.Icc (n - (m : ℤ)) n, ⋃ w ∈ fillingIndex q n
            (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r,
              adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate q (n + l) y)).toReal * C :=
      add_le_add (hT (n - (m : ℤ)) (by omega)) le_rfl
    _ ≤ T + (R * (1 / 3 : ℝ) ^ m) * C :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hres hC0)
    _ = T + R * C * (1 / 3 : ℝ) ^ m := by ring

end

end Transport
end HighContrast
end Homogenization
