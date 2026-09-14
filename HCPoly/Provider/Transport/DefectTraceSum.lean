/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.PositiveGapClosure

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The `L¹` seminorm of a nonnegative integrable scalar is its expectation. -/
theorem eLpNorm_one_eq_ofReal_integral {P : Measure (CoeffSpace d)}
    {f : CoeffSpace d → ℝ} (hf : Integrable f P) (hf0 : ∀ a, 0 ≤ f a) :
    eLpNorm f 1 P = ENNReal.ofReal (∫ a, f a ∂P) := by
  have hnorm : ∫ a, ‖f a‖ ∂P = ∫ a, f a ∂P :=
    integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => Real.norm_of_nonneg (hf0 a))
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hf, hnorm]

/-- The collective trace defect has exactly the sum of the mean trace defects as its `L¹` norm. -/
theorem eLpNorm_defect_trace_sum_eq {P : Measure (CoeffSpace d)}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) {Q : ℝ}
    (wt p : ι → ℝ) (D : ι → CoeffSpace d → BlockMat d) (H K : ι → BlockMat d)
    (hwt : ∀ i ∈ s, 0 ≤ wt i) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hDpos : ∀ i ∈ s, ∀ a, (toFullBlockMat (D i a)).PosSemidef)
    (hDint : ∀ i ∈ s, Integrable (fun a => toFullBlockMat (D i a)) P)
    (hDmean : ∀ i ∈ s, ∫ a, toFullBlockMat (D i a) ∂P =
      toFullBlockMat (blockSub (K i) (H i))) :
    eLpNorm (fun a => ∑ i ∈ s,
        wt i ^ Q * p i ^ (Q - 1) * blockTrace (D i a)) 1 P =
      ENNReal.ofReal (∑ i ∈ s,
        wt i ^ Q * p i ^ (Q - 1) * blockTrace (blockSub (K i) (H i))) := by
  have hcoef0 : ∀ i ∈ s, 0 ≤ wt i ^ Q * p i ^ (Q - 1) := fun i hi =>
    mul_nonneg (Real.rpow_nonneg (hwt i hi) _) (Real.rpow_nonneg (hp i hi) _)
  have htrace0 : ∀ i ∈ s, ∀ a, 0 ≤ blockTrace (D i a) := fun i hi a =>
    (hDpos i hi a).trace_nonneg
  have hint : Integrable (fun a => ∑ i ∈ s,
      wt i ^ Q * p i ^ (Q - 1) * blockTrace (D i a)) P :=
    integrable_finsetSum s fun i hi =>
      (Recurrence.integrable_blockTrace (hDint i hi)).const_mul _
  rw [eLpNorm_one_eq_ofReal_integral hint (fun a => Finset.sum_nonneg fun i hi =>
    mul_nonneg (hcoef0 i hi) (htrace0 i hi a))]
  congr 1
  rw [integral_finsetSum s fun i hi =>
    (Recurrence.integrable_blockTrace (hDint i hi)).const_mul _]
  exact Finset.sum_congr rfl fun i hi => by
    rw [integral_const_mul, Recurrence.integral_blockTrace (hDint i hi), hDmean i hi]
    rfl

end Transport
end HighContrast
end Homogenization
