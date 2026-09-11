/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.SmallContrastWeakAverageVariance
import HCPoly.Provider.Quenched.SmallContrastWeakEnergyTail
import HCPoly.Provider.Quenched.SmallContrastCenterVariance
import HCPoly.Provider.Response.ProfileWeakFullLp
import HCPoly.Provider.Response.ProfileSkewMeasurability

/-!
# The weak cap: the primal weak root by the per-scale carriers

The sample-level majorization of the primal weak root, at the
recentered samples and the inflated reference, with every group discharged
by the per-scale variance carriers, the mean drops, the decayed bad-energy
majorant, the geometric good-energy tail, and the terminal centering
variance.  No window multiplier, no coupled window, no history.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The per-scale budget of the weak cap: the two single-cell fluctuation
carriers and the deterministic mean drop at depth `j` below `t`. -/
def weakScaleBudget (P : Measure (CoeffSpace d)) (q : Mat d)
    (F : BlockMat d) (t : ℤ) (j : ℕ) : ℝ≥0∞ :=
  scaleVariance P q F (t - (j : ℤ)) + scaleVariance P q F t +
    ENNReal.ofReal
      (blockSize
        (blockSub (adaptedMean P q (t - (j : ℤ))) (adaptedMean P q t)) F)

end

end Homogenization.HighContrast.Quenched
