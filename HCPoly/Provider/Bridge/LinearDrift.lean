/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.TraceGap
import HCPoly.Provider.Recurrence.PositiveGapClosure

/-!
# Positivity of the linear determinant drift

The adapted means decrease in the Loewner order as the scale grows.  Therefore
every increment paired with the inverse terminal mean has nonnegative trace,
and so does the weighted linear drift.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- Every summand of the linear determinant drift is nonnegative on a finite
stationary adapted-mean window. -/
theorem linearDrift_nonneg [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {b T : ℤ} (hlb : l ≤ b)
    (hbT : b ≤ T)
    (hfin : ∀ j : ℤ, b ≤ j → j ≤ T → HasFiniteAdaptedMean P q j)
    (rho : ℝ) :
    0 ≤ linearDrift P rho q b T := by
  have hET : (toFullBlockMat (adaptedMean P q T)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq T (hfin T hbT le_rfl)
  rw [linearDrift]
  exact Finset.sum_nonneg fun r hr => by
    have hrange := Finset.mem_Icc.mp hr
    have hbrm : b ≤ r - 1 := by omega
    have hrT : r ≤ T := hrange.2
    have hmean :
        toFullBlockMat (adaptedMean P q r) ≤
          toFullBlockMat (adaptedMean P q (r - 1)) :=
      Recurrence.toFullBlockMat_adaptedMean_le hP hq (le_trans hlb hbrm) (by omega)
        (hfin (r - 1) hbrm (by omega)) (hfin r (by omega) hrT)
    have hdiff :
        (toFullBlockMat
          (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r))).PosSemidef := by
      rw [Recurrence.toFullBlockMat_blockSub]
      exact Matrix.le_iff.mp hmean
    have htrace :
        0 ≤ blockTrace
          (ofFullBlockMat
            ((toFullBlockMat (adaptedMean P q T))⁻¹ *
              toFullBlockMat
                (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r)))) := by
      rw [blockTrace, toFullBlockMat_ofFullBlockMat]
      exact PortableHistory.trace_mul_nonneg hET.inv.posSemidef hdiff
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) htrace

end

end Bridge
end HighContrast
end Homogenization
