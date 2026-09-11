/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.FixedGridWindowAccount
import HCPoly.Provider.Quenched.SmallContrastAbsorptionChoice
import HCPoly.Provider.Quenched.SmallContrastAdjointMirrors
import HCPoly.Provider.Quenched.SmallContrastAlignedGeometry
import HCPoly.Provider.Quenched.SmallContrastAnnealedEnvelope
import HCPoly.Provider.Quenched.SmallContrastAverageDrops
import HCPoly.Provider.Quenched.SmallContrastCenteringCap
import HCPoly.Provider.Quenched.SmallContrastEntryCapsIsotropy
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope
import HCPoly.Provider.Quenched.SmallContrastEntrySupply
import HCPoly.Provider.Quenched.SmallContrastFusionStep
import HCPoly.Provider.Quenched.SmallContrastHvarFamily
import HCPoly.Provider.Quenched.SmallContrastIsotropyPack
import HCPoly.Provider.Quenched.SmallContrastLoadScalePiFree
import HCPoly.Provider.Quenched.SmallContrastMeanDropCarrier
import HCPoly.Provider.Quenched.SmallContrastOneStepHub
import HCPoly.Provider.Quenched.SmallContrastRealClauses
import HCPoly.Provider.Quenched.SmallContrastRowAtCenters
import HCPoly.Provider.Quenched.SmallContrastSingleCellVariance
import HCPoly.Provider.Quenched.SmallContrastSlotValue
import HCPoly.Provider.Quenched.SmallContrastTerminalComparability
import HCPoly.Provider.Quenched.SmallContrastVarianceLagged
import HCPoly.Provider.Quenched.SmallContrastWeakCap
import HCPoly.Provider.Quenched.SmallContrastWeakValue
import HCPoly.Provider.Response.DiagonalWeakNormAdjointAlgebra
import HCPoly.Provider.Response.PreYoungFixedGridCells
import HCPoly.Provider.Response.ProfileRowOscillationSum
import HCPoly.Provider.Response.ProfileRowSchur
import HCPoly.Provider.Response.ProfileRowSkewCarriers

/-!
# The family's output *is* the fused core's `hone` slot

The last joint between's two halves, and it is free.

`exists_one_step_family_at_isotropy_var_at_level_conv_family_min` reports each generation's step with the
excess written `hatExcessAt P q ((N₀ : ℤ) + (n : ℤ))`;
the isotropic account core body's `hone` binder writes the same quantity
expanded, as `(d : ℝ) * (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)`.
Those are the two sides of `hatExcessAt`'s definition
(`HCPoly.Provider.Quenched.SmallContrastSmallnessPack`), so the joint is definitional.

`hone_of_one_step_family_isotropy` below checks it: **its proof is `h`**, so
its type-checking is the verification.  With it, the endpoint's
`hone` slot is filled by the family with no conversion layer at all — the
generation-step conversion is gone entirely.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- **The joint.**  The one-step family's report, at the isotropy row carrier, is
the fused core's `hone` hypothesis on the nose. -/
theorem hone_of_one_step_family_isotropy {d : ℕ} {Cpre eta : ℝ} {H : ℕ}
    {P : Measure (CoeffSpace d)} {q : Mat d} {N₀ ns : ℕ}
    {cRow kap : ℝ} {wv : ℕ → ℝ}
    (h : ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
        4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
              (16 * (d : ℝ) *
                (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                  adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
            rowValue2Isotropy d cRow kap
              (hatExcessAt P q ((N₀ : ℤ) + (n : ℤ))) + wv n) +
          2 * ((3 * (d : ℝ) + 4) *
            hatExcessAt P q ((N₀ : ℤ) + (n : ℤ)) ^ 2)) :
    ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
        4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
              (16 * (d : ℝ) *
                (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                  adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
            rowValue2Isotropy d cRow kap
                ((d : ℝ) *
                (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) + wv n) +
          2 * ((3 * (d : ℝ) + 4) *
            ((d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) ^ 2) := h

end

end Homogenization.HighContrast.Quenched
