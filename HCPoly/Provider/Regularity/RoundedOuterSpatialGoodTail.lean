/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.RoundedOuterSpatialWeakError
import HCPoly.Provider.Transport.DiscreteConvolution

/-!
# Rounded outer spatial good tails

The physical weak errors on base-rounded outer cells form the finite rows in
the manuscript's good event.  The common quantitative affine scale supplies
the first triadic generation from which every such row is summable.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Every finite row of base-rounded spatial weak errors beginning at `n` is
bounded by `delta`. -/
def BaseRoundedSpatialGoodTail [NeZero d]
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s delta : ℝ) (n : ℤ) : Prop :=
  ∀ m, n ≤ m →
    (∑ k ∈ Finset.Icc n m,
      baseRoundedSpatialWeakError a abar hS s k) ≤ delta

end

end Transport

noncomputable section

variable {d : ℕ}

private theorem physical_ratio_rpow_le_geometric_gap
    {x kappa : ℝ} {n k : ℤ} (hx : 0 < x)
    (hxn : x ≤ (3 : ℝ) ^ n) (hkappa : 0 < kappa) :
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
      (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
  have hkpow : 0 < (3 : ℝ) ^ k := by positivity
  have hratio : 0 < ((3 : ℝ) ^ k) / x := div_pos hkpow hx
  have hgap : 0 < (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) := by positivity
  have hbase :
      (3 : ℝ) ^ ((k : ℝ) - (n : ℝ)) ≤ ((3 : ℝ) ^ k) / x := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
      Real.rpow_intCast, Real.rpow_intCast]
    exact div_le_div_of_nonneg_left hkpow.le hx hxn
  calc
    (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
        ((3 : ℝ) ^ ((k : ℝ) - (n : ℝ))) ^ (-kappa) :=
      (Real.rpow_le_rpow_iff_of_neg hratio hgap
        (neg_neg_of_pos hkappa)).2 hbase
    _ = (3 : ℝ) ^ (((k : ℝ) - (n : ℝ)) * (-kappa)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    _ = (3 : ℝ) ^ (-kappa * ((k : ℝ) - (n : ℝ))) := by
      congr 1
      ring

end

end HighContrast
end Homogenization
