/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationAssembly

/-!
# The terminal nonlinear row against an earlier portable profile

The real terminal row occurring in the finite target-gap budget is exactly the
nonlinear history at the old terminal scale.  Portable majorization then moves
it back to the checkpoint profile.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The unshifted nonlinear terminal sum is controlled by the portable profile
at any earlier checkpoint in the same finite window. -/
theorem nonlinear_terminal_sum_le_portableProfile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {jStar TMax : ℤ} {Q a rhoMax : ℝ}
    (hQ : 0 < Q) (ha : 0 < a) (hadm : a ≤ Q * rhoMax - (d : ℝ))
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ TMax → HasFiniteAdaptedMean P q r)
    {b t : ℤ} (hjb : jStar ≤ b) (hbt : b ≤ t) (ht : t ≤ TMax) :
    ENNReal.ofReal
        (∑ r ∈ Finset.Ico jStar t,
          (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) *
            frakH Q (relMean P q r t)) ≤
      ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) *
        portableProfile P Q a rhoMax q jStar b t := by
  have hterm0 : ∀ r ∈ Finset.Ico jStar t,
      0 ≤ (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) *
        frakH Q (relMean P q r t) := by
    intro r hr
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (PortableHistory.frakH_relMean_nonneg hQ.le hP hq hlj hfin
        (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2.le ht)
  calc
    ENNReal.ofReal
        (∑ r ∈ Finset.Ico jStar t,
          (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) *
            frakH Q (relMean P q r t)) =
        nonlinearHistory P Q a q jStar t := by
      rw [nonlinearHistory, ENNReal.ofReal_sum_of_nonneg hterm0]
    _ ≤ portableHistory P Q a rhoMax q jStar t := by
      rw [portableHistory]
      exact le_add_left le_rfl
    _ ≤ ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) *
          portableProfile P Q a rhoMax q jStar b t :=
      PortableHistory.portable_majorization hQ ha hadm hP hq hlj hfin hjb hbt ht

end

end Transport
end HighContrast
end Homogenization
