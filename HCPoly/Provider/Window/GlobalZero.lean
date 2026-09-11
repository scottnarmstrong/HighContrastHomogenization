/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.AdaptedRows
import HCPoly.Provider.Initialization.Reference

/-!
# Global response rows at zero growth exponent

At exponent zero, the coarse-ellipticity discount is one.  For each fixed
sample and standard cell, a sufficiently large centered cube simultaneously
contains the cell center, lies above the cell scale, and exceeds the source
burn.  The resulting global standard rows feed the adapted-cell filling.
-/

namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-- At zero growth exponent, coarse ellipticity gives simultaneous global
standard and rounded adapted response rows on one event of full measure. -/
theorem ae_global_response_rows_zero
    (hd : 2 ≤ d) {Q K : ℝ} {jStar M : ℤ}
    (hwindow : IsCoupledWindow d Q K jStar M)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {P : Measure (CoeffSpace d)} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P 0 E Ψ K S) :
    ∀ᵐ a ∂P,
      (∀ (k : ℤ) (w : Fin d → ℤ),
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a) E ∧
          BlockMatLoewnerLE (coarseStarInv (standardCell d k w) a)
            (blockReflect E)) ∧
      (∀ n : Mat d, n.PosDef → ∀ (r : ℤ) (y : Vec d),
        BlockMatLoewnerLE
            (coarseBlock (adaptedCellTranslate (roundedGrid jStar n) r y) a)
            (blockScale (boundaryConst Cd 0 n) E) ∧
          BlockMatLoewnerLE
            (coarseStarInv (adaptedCellTranslate (roundedGrid jStar n) r y) a)
            (blockScale (boundaryConst Cd 0 n) (blockReflect E))) := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hburn : (kZero d : ℤ) ≤ sourceBurn d Q K := by
    rw [sourceBurn]
    exact le_max_left _ _
  have hj : (kZero d : ℤ) ≤ jStar := hburn.trans hwindow.1
  filter_upwards [hdag.coarse_bound] with a ha
  have hstandard : ∀ (k : ℤ) (w : Fin d → ℤ),
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a) E := by
    intro k w
    let R : ℝ := max (S a)
      (2 * ∑ i : Fin d, |standardCellCenter k w i|)
    obtain ⟨n, hn⟩ :=
      pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 3)
    have hnz : R < (3 : ℝ) ^ (n : ℤ) := by
      rwa [zpow_natCast]
    let m : ℤ := max k (n : ℤ)
    have hkm : k ≤ m := le_max_left _ _
    have hnm : (n : ℤ) ≤ m := le_max_right _ _
    have hpownm : (3 : ℝ) ^ (n : ℤ) ≤ (3 : ℝ) ^ m :=
      zpow_le_zpow_right₀ (by norm_num) hnm
    have hsource : S a ≤ (3 : ℝ) ^ m :=
      (le_max_left _ _).trans (hnz.le.trans hpownm)
    have hcenter : standardCellCenter k w ∈ centeredCube d m := by
      rw [Recurrence.mem_centeredCube_iff]
      intro i
      have hi : |standardCellCenter k w i| ≤
          ∑ j : Fin d, |standardCellCenter k w j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (standardCellCenter k w j))
          (Finset.mem_univ i)
      have habs : 2 * |standardCellCenter k w i| < (3 : ℝ) ^ m := by
        calc
          2 * |standardCellCenter k w i| ≤
              2 * ∑ j : Fin d, |standardCellCenter k w j| :=
            mul_le_mul_of_nonneg_left hi (by norm_num)
          _ ≤ R := le_max_right _ _
          _ < (3 : ℝ) ^ (n : ℤ) := hnz
          _ ≤ (3 : ℝ) ^ m := hpownm
      have habs' : |standardCellCenter k w i| <
          (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
        linarith only [habs]
      simpa only [neg_mul] using (abs_lt.mp habs')
    have hcell := ha m hsource k hkm w hcenter
    simpa only [zero_mul, Real.rpow_zero, blockScale_one] using hcell
  constructor
  · intro k w
    have hprimal := hstandard k w
    refine ⟨hprimal, ?_⟩
    simpa only [Transport.coarseStarInv_eq_blockReflect] using
      Transport.blockMatLoewnerLE_blockReflect hprimal
  · intro n hn r y
    have hrows := adapted_rows_of_standard (a := a) (E := E) hd hdag.g_mem hj hCd hn
      hdag.refBlock_posDef (Y := 1) zero_le_one r y (by
        intro k w _hcell
        simpa only [burnDiscount, zero_mul, Real.rpow_zero, one_mul, blockScale_one] using
          hstandard k w)
    simpa only [burnDiscount, zero_mul, Real.rpow_zero, mul_one] using hrows

end

end Window
end HighContrast
end Homogenization
