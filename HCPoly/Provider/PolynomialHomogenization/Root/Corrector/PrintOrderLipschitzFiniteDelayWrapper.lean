/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
import HCPoly.Provider.PolynomialHomogenization.DecoupledRootCertificatePair
import HCPoly.Provider.PolynomialHomogenization.Root.Corrector.PrintOrderLipschitzScaleComparison

/-!
# Root certificate to printed finite-delay data

The printed-order certificate produces the selected-generation terminal
surface, and its recurrence start differs from the root start by one
deterministic delay.
-/

namespace Homogenization
namespace HighContrast
namespace Root

open Set
open Certificate

noncomputable section

/-- A root-facing printed certificate supplies one selected-generation finite
terminal and a law-free comparison of its start index with the root index. -/
theorem exists_printOrderRootFiniteDelaySurface
    (d : ℕ) [NeZero d] :
    ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 →
      ∃ (C c Cid : ℝ),
        1 ≤ C ∧ c = (2 * C)⁻¹ ∧ c ∈ Ioo (0 : ℝ) 1 ∧
        ∀ (kappa : ℝ) (abar : Mat d) (a : CoeffSpace d) (x : ℝ),
          PrintOrderRateBearingCommonAffineGoodScale
              d g c kappa abar a x →
            ∃ surface : PrintOrderDecoupledFiniteTerminalSurface
                d g c kappa Cid abar a x,
              Quenched.triadicCeilingIndex
                  (printOrderCommonQuantitativeAffineScale d g
                    surface.sourceAmplitude
                    (correctorTargetAmplitude c kappa) kappa abar
                    surface.X a) ≤
                Quenched.triadicCeilingIndex x +
                  Quenched.triadicCeilingIndex
                    (printOrderToBaseResponseScaleFactor d g kappa) := by
  intro g hg
  obtain ⟨Cid, hidentity⟩ :=
    exists_printOrderIdentityCubeDualRegularityWithConstant d g hg
  obtain ⟨C, c, hC, hc, hcRange, hsurface⟩ :=
    exists_printOrderDecoupledFiniteTerminalSurface
      d g Cid hg hidentity
  refine ⟨C, c, Cid, hC, hc, hcRange, ?_⟩
  intro kappa abar a x hgood
  obtain ⟨surface⟩ := hsurface kappa abar a x hgood
  exact ⟨surface,
    Homogenization.HighContrast.Root.PrintOrderDecoupledFiniteTerminalSurface.printOrderStartIndex_le_rootStart_add_delay
      surface hg⟩

/-- The same finite-delay package is available from the root's paired
qualitative and printed-order certificate. -/
theorem exists_decoupledRootFiniteDelaySurface
    (d : ℕ) [NeZero d] :
    ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 →
      ∃ (C c Cid : ℝ),
        1 ≤ C ∧ c = (2 * C)⁻¹ ∧ c ∈ Ioo (0 : ℝ) 1 ∧
        ∀ (kappa : ℝ) (abar : Mat d) (a : CoeffSpace d) (x : ℝ),
          DecoupledRootGoodScale d g c kappa abar a x →
            ∃ surface : PrintOrderDecoupledFiniteTerminalSurface
                d g c kappa Cid abar a x,
              Quenched.triadicCeilingIndex
                  (printOrderCommonQuantitativeAffineScale d g
                    surface.sourceAmplitude
                    (correctorTargetAmplitude c kappa) kappa abar
                    surface.X a) ≤
                Quenched.triadicCeilingIndex x +
                  Quenched.triadicCeilingIndex
                    (printOrderToBaseResponseScaleFactor d g kappa) := by
  intro g hg
  obtain ⟨C, c, Cid, hC, hc, hcRange, hsurface⟩ :=
    exists_printOrderRootFiniteDelaySurface d g hg
  refine ⟨C, c, Cid, hC, hc, hcRange, ?_⟩
  intro kappa abar a x hgood
  exact hsurface kappa abar a x hgood.to_printOrder

end

end Root
end HighContrast
end Homogenization
