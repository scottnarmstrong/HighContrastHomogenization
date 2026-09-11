/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalDefinition

/-!
# What the reconciled-smallness certificate hands the deterministic holes

Two of the three premises of the C¹ slope approximation at the exact-gauge
terminal are discharged from the certificate itself; only the exact-gauge
terminal remains.
-/

namespace Homogenization
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The `c`-parameterised certificate carries the positive-definiteness of the
homogenized symmetric part, exactly as `RootInterface.RootGoodScale` does. -/
theorem rootGoodScaleAt_posDef [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x : ℝ}
    (h : rootGoodScaleAt d g c kappaRate abar a x) :
    (symmPart abar).PosDef := by
  obtain ⟨hh, -, -⟩ := h
  obtain ⟨amp, Xc, hcert, -⟩ := hh.good
  obtain ⟨hS, -⟩ := hcert
  exact hS

end

end CorrectorComposition
end HighContrast
end Homogenization
