/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationSup

/-!
# Moment of a finite maximum

A pathwise maximum over finitely many nonnegative random variables is charged
to the sum of their moments.  This is the union-bound step used only for the
fresh part of the transported cell majorants.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- The `Q`-th moment of a nonempty finite maximum is at most the sum of the
individual `Q`-th moments. -/
theorem lintegral_finset_sup'_rpow_le_sum {ι α : Type*} [DecidableEq ι]
    [MeasurableSpace α] (P : Measure α) (s : Finset ι) (hs : s.Nonempty)
    {Q : ℝ} (f : ι → α → ℝ)
    (hfmeas : ∀ i ∈ s,
      AEMeasurable (fun x => ENNReal.ofReal (f i x) ^ Q) P) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i => f i x) ^ Q ∂P ≤
      ∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (f i x) ^ Q ∂P := by
  have hpath : ∀ x,
      ENNReal.ofReal (s.sup' hs fun i => f i x) ^ Q ≤
        ∑ i ∈ s, ENNReal.ofReal (f i x) ^ Q := by
    intro x
    obtain ⟨i, hi, hmax⟩ := s.exists_mem_eq_sup' hs (fun i => f i x)
    rw [hmax]
    exact Finset.single_le_sum
      (f := fun k => ENNReal.ofReal (f k x) ^ Q)
      (fun _ _ => (zero_le _ : (0 : ℝ≥0∞) ≤ _)) hi
  refine (lintegral_mono hpath).trans_eq ?_
  exact lintegral_finset_sum' s hfmeas

end

end Transport
end HighContrast
end Homogenization
