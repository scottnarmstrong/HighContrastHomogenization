/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.DriftAccount
import HCPoly.Provider.Transport.WindowDefinedness

/-!
# What the window guarantees about one grid tower

`p.successful.short.bridge` states no definedness hypothesis and
exports no definedness conclusion.  The semantic guard chain supplies both:
whenever the adapted cells of a rounded grid over a range of scales lie inside
the preassigned window, the window multiplier makes the annealed blocks of that
grid finite and positive definite on exactly those scales, orders them, and
therefore makes the linear drift nonnegative.

The three statements below are the form of that chain the short test reads.
They are single-tower statements: the two towers of the proposition are handled
by applying them twice, once at the old witness and once at the candidate, and
the candidate's own positivity is established before either application.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- **The annealed blocks of a tower inside the window are positive definite.**
-/
theorem posDef_adaptedMean_of_window {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    {b j : ℤ} (hj : jStar ≤ j) (hjb : j ≤ b)
    (hcont : ∀ j : ℤ, jStar ≤ j → j ≤ b →
      adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) :
    (toFullBlockMat (adaptedMean P (roundedGrid jStar nu) j)).PosDef :=
  Recurrence.posDef_toFullBlockMat_adaptedMean
    (Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hnu) j
    (Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu
      (Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hnu) hj (hcont j hj hjb))

/-- **The annealed blocks of a tower inside the window are ordered**, in the
flattened dialect. -/
theorem adaptedMean_le_of_window [NeZero d] {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K Cd Q : ℝ} {jStar M : ℤ} (hw : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {nu : Mat d} (hnu : nu.PosDef) {b j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hTb : T ≤ b)
    (hcont : ∀ j : ℤ, jStar ≤ j → j ≤ b →
      adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) :
    toFullBlockMat (adaptedMean P (roundedGrid jStar nu) T) ≤
      toFullBlockMat (adaptedMean P (roundedGrid jStar nu) j) := by
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hnu
  exact Recurrence.toFullBlockMat_adaptedMean_le hstat hq hj hjT
    (Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq hj (hcont j hj (hjT.trans hTb)))
    (Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq (hj.trans hjT) (hcont T
      (hj.trans hjT) hTb))

/-- **The linear drift of a tower inside the window is nonnegative.**  The mean
order supplies a positive semidefinite increment at every scale of the range. -/
theorem linearDrift_nonneg_of_window [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    {rhoDr : ℝ} {b T : ℤ} (hT : jStar ≤ T) (hTb : T ≤ b)
    (hcont : ∀ j : ℤ, jStar ≤ j → j ≤ b →
      adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) :
    0 ≤ linearDrift P rhoDr (roundedGrid jStar nu) jStar T := by
  refine linearDrift_nonneg (posDef_adaptedMean_of_window hw hY hnu hT hTb hcont)
    fun r hr1 hr2 => ?_
  exact adaptedMean_le_of_window hstat hw hY hnu (by omega) (by omega)
    (le_trans hr2 hTb) hcont

end

end ShortHop
end HighContrast
end Homogenization
