/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowDefinedness
import HCPoly.Provider.Recurrence.MeanOrder
import HCPoly.Setup.Exponents
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Structural initialization facts from a window multiplier

These are the clauses of `p.initial.fixed.grid.scale` that use
only the coupled window, the common multiplier, and the available fixed-grid
toolkit.  The quantitative two-sided and moment estimates are kept separate.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The initialization exponent is at least two when the source exponent is
strictly below one. -/
theorem two_le_initExpQ {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    (2 : ℝ) ≤ ((initExpQ d g : ℕ) : ℝ) := by
  exact_mod_cast InitializationExponents.two_le_initExpQ d hg.2

/-- On a probability space, the integral of a nonnegative multiplier is below
each of its `L^Q` norms for `Q ≥ 1`. -/
theorem ofReal_integral_le_lqNorm {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {Q : ℝ} (hQ : 1 ≤ Q) :
    ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y := by
  have hint : Integrable Y P := Transport.integrable_of_isWindowMultiplier hY
  have hint_nonneg : 0 ≤ ∫ a, Y a ∂P :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun a =>
      le_trans zero_le_one (hY.one_le a))
  calc
    ENNReal.ofReal (∫ a, Y a ∂P) = ‖∫ a, Y a ∂P‖ₑ := by
      rw [Real.enorm_eq_ofReal hint_nonneg]
    _ ≤ eLpNorm Y 1 P := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact enorm_integral_le_lintegral_enorm Y
    _ ≤ lqNorm P Q Y := by
      unfold lqNorm
      exact eLpNorm_le_eLpNorm_of_exponent_le
        (by simpa using ENNReal.ofReal_le_ofReal hQ) hY.measurable.aestronglyMeasurable

/-- Above the alignment scale, the burn discount in a window multiplier is
one. -/
theorem burnDiscount_eq_one {g : ℝ} {jStar r : ℤ} (hr : jStar ≤ r) :
    burnDiscount g jStar r = 1 := by
  have hle : ((jStar : ℝ) - (r : ℝ)) ≤ 0 := by
    have hcast : (jStar : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith only [hcast]
  rw [burnDiscount, max_eq_right hle, mul_zero, Real.rpow_zero]

/-- The simultaneous pathwise clause of initialization is already present in
the primal and adjoint fields of the window multiplier. -/
theorem ae_adaptedResponse_and_coarseStarInv_le {P : Measure (CoeffSpace d)}
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ}
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) :
    ∀ᵐ a ∂P, ∀ mu : Mat d, mu.PosDef → ∀ (r : ℤ) (w : Fin d → ℤ),
      IsAdmissibleIndex (roundedGrid jStar mu) jStar M r w →
        BlockMatLoewnerLE (adaptedResponse (roundedGrid jStar mu) r w a)
            (blockScale (boundaryConst Cd g mu * Y a) E) ∧
          BlockMatLoewnerLE
            (coarseStarInv (adaptedCellAt (roundedGrid jStar mu) r w) a)
            (blockScale (boundaryConst Cd g mu * Y a) (blockReflect E)) := by
  filter_upwards [hY.adapted_primal, hY.adapted_adjoint] with a hprimal hadjoint
  intro mu hmu r w hindex
  obtain ⟨hr, hcell, -⟩ := hindex
  have hburn := burnDiscount_eq_one (g := g) hr
  have htranslate :
      adaptedCellTranslate (roundedGrid jStar mu) r
          (adaptedCellCenter (roundedGrid jStar mu) r w) =
        adaptedCellAt (roundedGrid jStar mu) r w :=
    (adaptedCellAt_eq_adaptedCellTranslate _ _ _).symm
  constructor
  · have h := hprimal mu hmu r (adaptedCellCenter (roundedGrid jStar mu) r w) (by
      rw [htranslate]
      exact hcell)
    rw [htranslate, hburn, mul_one] at h
    simpa only [adaptedResponse] using h
  · have h := hadjoint mu hmu r (adaptedCellCenter (roundedGrid jStar mu) r w) (by
      rw [htranslate]
      exact hcell)
    rwa [htranslate, hburn, mul_one] at h

/-- Finiteness and positivity of every admissible deterministic cell follow
from the multiplier without any quantitative moment estimate. -/
theorem finite_and_posDef_of_admissible {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {Q g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K Cd : ℝ} {jStar M : ℤ} (hw : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu : Mat d} (hmu : mu.PosDef) {r : ℤ} {w : Fin d → ℤ}
    (hindex : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r w) :
    HasFiniteAdaptedMean P (roundedGrid jStar mu) r ∧
      Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid jStar mu) r) := by
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  exact ⟨Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hmu hq hindex.1 hindex.2.2,
    Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hmu hq hindex.1 hindex.2.2⟩

/-- The ordered-mean and nonnegative determinant clauses for two admissible
scales are direct consumers of the fixed-grid recurrence toolkit. -/
theorem mean_order_and_detIncrement_nonneg [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) {Q g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {mu : Mat d}
    (hmu : mu.PosDef) {r T : ℤ} (hrT : r ≤ T)
    (hr : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r 0)
    (hT : IsAdmissibleIndex (roundedGrid jStar mu) jStar M T 0) :
    BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar mu) T)
        (adaptedMean P (roundedGrid jStar mu) r) ∧
      0 ≤ detIncrement P (roundedGrid jStar mu) r T := by
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  have hfinr := Transport.hasFiniteAdaptedMean_of_isWindowMultiplier
    hY hmu hq hr.1 hr.2.2
  have hfinT := Transport.hasFiniteAdaptedMean_of_isWindowMultiplier
    hY hmu hq hT.1 hT.2.2
  exact ⟨Recurrence.adaptedMean_le hP hq hr.1 hrT hfinr hfinT,
    Recurrence.detIncrement_nonneg hP hq hr.1 hrT hfinr hfinT⟩

end

end Initialization
end HighContrast
end Homogenization
