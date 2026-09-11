/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridTube

/-!
# The hybrid tube row

The two coordinate changes in the packed-boundary tube are absorbed together
into the symmetric cross-grid factor.  The resulting estimate has the extra
scale-row decay needed by the reverse hybrid filling.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem norm_inv_mul_self_of_posDef [NeZero d] {q : Mat d}
    (hq : q.PosDef) : ‖q⁻¹ * q‖ = 1 := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  rw [Matrix.nonsing_inv_mul _ hdet, norm_one]

private theorem hybrid_tube_coefficient_le (hd : 2 ≤ d) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    2 * (d : ℝ) * Real.sqrt d +
        (2 * (d : ℝ) * Real.sqrt d * B *
            (1 + 6 * Real.sqrt d * B) ^ (d - 1)) *
          (2 * (d : ℝ) * Real.sqrt d * (2 * A + 1)) ≤
      (2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d) *
            (2 * (d : ℝ) * Real.sqrt d) * 2 *
              (1 + 6 * Real.sqrt d) ^ (d - 1)) *
        (1 + A + B) ^ (2 * d) := by
  let R : ℝ := 1 + A + B
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    linarith only [hA, hB]
  have hAR : A ≤ R := by
    dsimp only [R]
    linarith only [hB]
  have hBR : B ≤ R := by
    dsimp only [R]
    linarith only [hA]
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hbase0 : 0 ≤ 1 + 6 * Real.sqrt d * B := by positivity
  have hbase : 1 + 6 * Real.sqrt d * B ≤
      (1 + 6 * Real.sqrt d) * R := by
    have hrest : 0 ≤ A + B + 6 * Real.sqrt d + 6 * Real.sqrt d * A := by
      positivity
    dsimp only [R]
    calc
      1 + 6 * Real.sqrt d * B ≤
          1 + 6 * Real.sqrt d * B +
            (A + B + 6 * Real.sqrt d + 6 * Real.sqrt d * A) :=
        le_add_of_nonneg_right hrest
      _ = (1 + 6 * Real.sqrt d) * (1 + A + B) := by ring
  have hpowbase : (1 + 6 * Real.sqrt d * B) ^ (d - 1) ≤
      ((1 + 6 * Real.sqrt d) * R) ^ (d - 1) :=
    pow_le_pow_left₀ hbase0 hbase (d - 1)
  have h2A : 2 * A + 1 ≤ 2 * R := by
    dsimp only [R]
    linarith only [hA, hB]
  have hRpow : R * R ^ (d - 1) * R ≤ R ^ (2 * d) := by
    calc
      R * R ^ (d - 1) * R = R ^ (1 + (d - 1) + 1) := by
        rw [pow_add, pow_add, pow_one]
      _ ≤ R ^ (2 * d) := pow_le_pow_right₀ hR1 (by omega)
  have houter : 2 * (d : ℝ) * Real.sqrt d ≤
      (2 * (d : ℝ) * Real.sqrt d) * R ^ (2 * d) := by
    have hpow1 : 1 ≤ R ^ (2 * d) := one_le_pow₀ hR1
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow1 (by positivity :
      0 ≤ 2 * (d : ℝ) * Real.sqrt d)
  have hinternal :
      (2 * (d : ℝ) * Real.sqrt d * B *
          (1 + 6 * Real.sqrt d * B) ^ (d - 1)) *
        (2 * (d : ℝ) * Real.sqrt d * (2 * A + 1)) ≤
      ((2 * (d : ℝ) * Real.sqrt d) *
          (2 * (d : ℝ) * Real.sqrt d) * 2 *
            (1 + 6 * Real.sqrt d) ^ (d - 1)) * R ^ (2 * d) := by
    calc
      (2 * (d : ℝ) * Real.sqrt d * B *
            (1 + 6 * Real.sqrt d * B) ^ (d - 1)) *
          (2 * (d : ℝ) * Real.sqrt d * (2 * A + 1))
          ≤ (2 * (d : ℝ) * Real.sqrt d * R *
              ((1 + 6 * Real.sqrt d) * R) ^ (d - 1)) *
            (2 * (d : ℝ) * Real.sqrt d * (2 * R)) := by
              gcongr
      _ = ((2 * (d : ℝ) * Real.sqrt d) *
              (2 * (d : ℝ) * Real.sqrt d) * 2 *
                (1 + 6 * Real.sqrt d) ^ (d - 1)) *
            (R * R ^ (d - 1) * R) := by
              rw [mul_pow]
              ring
      _ ≤ ((2 * (d : ℝ) * Real.sqrt d) *
              (2 * (d : ℝ) * Real.sqrt d) * 2 *
                (1 + 6 * Real.sqrt d) ^ (d - 1)) * R ^ (2 * d) := by
              gcongr
  linarith only [houter, hinternal]

/-- The packed-boundary tube has the cross-grid row decay of
`e.two.grid.whitney.reverse.volumes`. -/
theorem volume_le_of_escaping_hybridStrip {q q' : Mat d} (hd : 2 ≤ d)
    (hq : q.PosDef) (hq' : q'.PosDef) {n l c : ℤ} (hcn : c ≤ n)
    (y : Vec d) {A : Set (Vec d)}
    (hA : A ⊆ hybridStrip q' n (adaptedCellTranslate q (n + l) y))
    (hesc : ∀ x ∈ A, ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
      ¬ adaptedCellAt q c v ⊆
        hybridStrip q' n (adaptedCellTranslate q (n + l) y)) :
    volume A ≤
      ENNReal.ofReal
          ((2 * (d : ℝ) * Real.sqrt d +
              (2 * (d : ℝ) * Real.sqrt d) *
                (2 * (d : ℝ) * Real.sqrt d) * 2 *
                  (1 + 6 * Real.sqrt d) ^ (d - 1)) *
            gridRatio q q' * (3 : ℝ) ^ (c - (n + l))) *
        volume (adaptedCellTranslate q (n + l) y) := by
  letI : NeZero d := ⟨by omega⟩
  have hself : ‖q⁻¹ * q‖ = 1 := norm_inv_mul_self_of_posDef hq
  have h3cn : (3 : ℝ) ^ c ≤ (3 : ℝ) ^ n :=
    zpow_le_zpow_right₀ (by norm_num) hcn
  have hlayer :
      2 * (d : ℝ) *
          (Real.sqrt d *
            (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n + (3 : ℝ) ^ c)) *
            (3 : ℝ) ^ (-(n + l)) ≤
        2 * (d : ℝ) * Real.sqrt d * (2 * ‖q⁻¹ * q'‖ + 1) *
          (3 : ℝ) ^ (-l) := by
    calc
      2 * (d : ℝ) *
            (Real.sqrt d *
              (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n + (3 : ℝ) ^ c)) *
              (3 : ℝ) ^ (-(n + l))
          ≤ 2 * (d : ℝ) *
            (Real.sqrt d *
              (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n + (3 : ℝ) ^ n)) *
              (3 : ℝ) ^ (-(n + l)) := by
                gcongr
      _ = 2 * (d : ℝ) * Real.sqrt d * (2 * ‖q⁻¹ * q'‖ + 1) *
            (3 : ℝ) ^ (-l) := by
              rw [show -l = n + -(n + l) by ring,
                zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
              ring
  have hscale : (3 : ℝ) ^ (c - n) * (3 : ℝ) ^ (-l) =
      (3 : ℝ) ^ (c - (n + l)) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hA0 : 0 ≤ ‖q⁻¹ * q'‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖q'⁻¹ * q‖ := norm_nonneg _
  have hcoef :
      2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
              (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1)) *
            (2 * (d : ℝ) * Real.sqrt d * (2 * ‖q⁻¹ * q'‖ + 1)) ≤
        (2 * (d : ℝ) * Real.sqrt d +
            (2 * (d : ℝ) * Real.sqrt d) *
              (2 * (d : ℝ) * Real.sqrt d) * 2 *
                (1 + 6 * Real.sqrt d) ^ (d - 1)) * gridRatio q q' := by
    simpa only [gridRatio] using hybrid_tube_coefficient_le hd hA0 hB0
  have hreal :
      2 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ (c - (n + l)) +
          (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
              (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                (3 : ℝ) ^ (c - n)) *
            (2 * (d : ℝ) * Real.sqrt d * (2 * ‖q⁻¹ * q'‖ + 1) *
              (3 : ℝ) ^ (-l)) ≤
        (2 * (d : ℝ) * Real.sqrt d +
            (2 * (d : ℝ) * Real.sqrt d) *
              (2 * (d : ℝ) * Real.sqrt d) * 2 *
                (1 + 6 * Real.sqrt d) ^ (d - 1)) *
          gridRatio q q' * (3 : ℝ) ^ (c - (n + l)) := by
    rw [← hscale]
    have hscale0 : 0 ≤ (3 : ℝ) ^ (c - n) * (3 : ℝ) ^ (-l) := by positivity
    convert mul_le_mul_of_nonneg_right hcoef hscale0 using 1
    all_goals ring
  have hraw := volume_le_of_escaping_hybridStrip_raw hq hq' hcn y hA hesc
  simp only [hself, one_mul, mul_one] at hraw
  refine hraw.trans ?_
  have hcollar0 : 0 ≤
      2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
        (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
        (3 : ℝ) ^ (c - n) := by positivity
  have htarget0 : 0 ≤
      2 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ (c - (n + l)) := by positivity
  have hsimple0 : 0 ≤
      2 * (d : ℝ) * Real.sqrt d * (2 * ‖q⁻¹ * q'‖ + 1) *
        (3 : ℝ) ^ (-l) := by positivity
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ (c - (n + l))) +
        ENNReal.ofReal
            (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
              (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                (3 : ℝ) ^ (c - n)) *
          ENNReal.ofReal
            (2 * (d : ℝ) *
              (Real.sqrt d *
                (2 * ‖q⁻¹ * q'‖ * (3 : ℝ) ^ n + (3 : ℝ) ^ c)) *
              (3 : ℝ) ^ (-(n + l)))
        ≤ ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ (c - (n + l))) +
            ENNReal.ofReal
              (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
                (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                  (3 : ℝ) ^ (c - n)) *
              ENNReal.ofReal
                (2 * (d : ℝ) * Real.sqrt d * (2 * ‖q⁻¹ * q'‖ + 1) *
                  (3 : ℝ) ^ (-l)) := by
            exact add_le_add le_rfl
              (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlayer))
    _ = ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ (c - (n + l)) +
            (2 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
                (1 + 6 * Real.sqrt d * ‖q'⁻¹ * q‖) ^ (d - 1) *
                  (3 : ℝ) ^ (c - n)) *
              (2 * (d : ℝ) * Real.sqrt d * (2 * ‖q⁻¹ * q'‖ + 1) *
                (3 : ℝ) ^ (-l))) := by
            rw [← ENNReal.ofReal_mul hcollar0,
              ← ENNReal.ofReal_add htarget0 (mul_nonneg hcollar0 hsimple0)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end

end Transport
end HighContrast
end Homogenization
