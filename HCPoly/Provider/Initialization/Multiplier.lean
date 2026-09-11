/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.Structural
import HCPoly.Provider.Window.MultiplierMoment

/-!
# The initialization multiplier display

The initialization exponent is admissible for the probability-space norm
comparison, while its coupled burn makes the weak-Orlicz moment at most two.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The exact two inequalities in the multiplier clause of
`p.initial.fixed.grid.scale`. -/
theorem initialization_multiplier_bounds
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K Cd : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) :
    ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P ((initExpQ d g : ℕ) : ℝ) Y ∧
      lqNorm P ((initExpQ d g : ℕ) : ℝ) Y ≤ 2 := by
  have hQ : (1 : ℝ) ≤ ((initExpQ d g : ℕ) : ℝ) :=
    le_trans (by norm_num) (two_le_initExpQ hg)
  exact ⟨ofReal_integral_le_lqNorm hY hQ, Window.lqNorm_le_two hQ hw hY⟩

end

end Initialization
end HighContrast
end Homogenization
