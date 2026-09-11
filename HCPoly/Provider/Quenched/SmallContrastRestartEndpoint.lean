/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.FixedGridWindowAccount
import HCPoly.Provider.Quenched.Prop42Scalar.DecayDelay
import HCPoly.Provider.Quenched.SmallContrastAbsorptionChoice
import HCPoly.Provider.Quenched.SmallContrastAdjointMirrors
import HCPoly.Provider.Quenched.SmallContrastAlignedGeometry
import HCPoly.Provider.Quenched.SmallContrastAnnealedEnvelope
import HCPoly.Provider.Quenched.SmallContrastAverageDrops
import HCPoly.Provider.Quenched.SmallContrastCenteringCap
import HCPoly.Provider.Quenched.SmallContrastDilation
import HCPoly.Provider.Quenched.SmallContrastDropRegroup
import HCPoly.Provider.Quenched.SmallContrastEntryCapsIsotropy
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope
import HCPoly.Provider.Quenched.SmallContrastEntryEstimates
import HCPoly.Provider.Quenched.SmallContrastEntryRateMean
import HCPoly.Provider.Quenched.SmallContrastEntrySupply
import HCPoly.Provider.Quenched.SmallContrastFusionStep
import HCPoly.Provider.Quenched.SmallContrastHatDecay
import HCPoly.Provider.Quenched.SmallContrastHvarFamily
import HCPoly.Provider.Quenched.SmallContrastMeanDropCarrier
import HCPoly.Provider.Quenched.SmallContrastOneStepHub
import HCPoly.Provider.Quenched.SmallContrastRealClauses
import HCPoly.Provider.Quenched.SmallContrastRecursionAssembly
import HCPoly.Provider.Quenched.SmallContrastRecursionShape
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
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The `hcore` body from a hatted decay, rather than from a recursion

The endpoint composition reads the recursion and runs the iteration lemma, so
its interface is `hinit`, `hsmall`, and `hrec`.  The
two-stage scheme does not produce a recursion at the restart base: it produces
the **decay** already, in the restart-base decay's shape

```
∀ n, hatExcess P q N₀' n ≤ Kpre * (3 : ℝ) ^ (-gam * (n : ℝ)) .
```

`hcore_body_of_hatted_decay` below is the outer composition read from that
shape.  Its proof is the endpoint composition's body with the iteration step
removed:
`hhat_all_of_hatted_decay` moves the decay to the `∀ n ≥ 2N₀` form that
`exists_annealed_decay_of_hhat_and_transfer` consumes, and the composition is
unchanged.

Both lemmas are reindexings of a given decay bound.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The hatted decay past `2N₀`, from a decay at the base.**  The literal
`hhat` hypothesis of `exists_annealed_decay_of_hhat_and_transfer`, read off a
geometric bound on the hatted excess rather than off a recursion. -/
theorem hhat_all_of_hatted_decay [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} {N₀ : ℕ} {Kpre gam : ℝ}
    (hKpre : 0 ≤ Kpre) (hgam0 : 0 < gam)
    (hdecay : ∀ n : ℕ,
      hatExcess P q N₀ n ≤ Kpre * (3 : ℝ) ^ (-gam * (n : ℝ))) :
    ∀ n : ℕ, 2 * N₀ ≤ n →
      (9 / 2 : ℝ) * ((d : ℝ) * (adaptedHattedContrast P q (n : ℤ) - 1)) ≤
        9 / 2 * Kpre *
          Real.rpow (3 : ℝ) (-gam * ((n - 2 * N₀ : ℕ) : ℝ)) := by
  intro n hn
  have hidx : ((N₀ : ℤ) + ((n - N₀ : ℕ) : ℤ)) = (n : ℤ) := by omega
  have hval : hatExcess P q N₀ (n - N₀) =
      (d : ℝ) * (adaptedHattedContrast P q (n : ℤ) - 1) := by
    rw [hatExcess, hidx]
  have hexp : ((n - 2 * N₀ : ℕ) : ℝ) ≤ ((n - N₀ : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega)
  have hmono : Real.rpow (3 : ℝ) (-gam * ((n - N₀ : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (-gam * ((n - 2 * N₀ : ℕ) : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have := mul_le_mul_of_nonneg_left hexp hgam0.le
    linarith only [this]
  have hchain : hatExcess P q N₀ (n - N₀) ≤
      Kpre * Real.rpow (3 : ℝ) (-gam * ((n - 2 * N₀ : ℕ) : ℝ)) :=
    le_trans (hdecay (n - N₀)) (mul_le_mul_of_nonneg_left hmono hKpre)
  rw [← hval]
  calc (9 / 2 : ℝ) * hatExcess P q N₀ (n - N₀)
      ≤ (9 / 2 : ℝ) *
          (Kpre * Real.rpow (3 : ℝ) (-gam * ((n - 2 * N₀ : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hchain (by norm_num)
    _ = 9 / 2 * Kpre *
          Real.rpow (3 : ℝ) (-gam * ((n - 2 * N₀ : ℕ) : ℝ)) := by ring

/-- **The `hcore` body from a hatted decay.**  The endpoint composition's
conclusion,
with the decay supplied rather than derived — the interface the two-stage scheme
delivers at the restart base. -/
theorem hcore_body_of_hatted_decay [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} {N₀ : ℕ} {Kpre gam : ℝ}
    (hKpre : 0 ≤ Kpre) (hgam0 : 0 < gam) (hgam1 : gam ≤ 1)
    (hdecay : ∀ n : ℕ,
      hatExcess P q N₀ n ≤ Kpre * (3 : ℝ) ^ (-gam * (n : ℝ)))
    {base Centry Cpref : ℝ} (hbase : 3 ≤ base) (hCpref : 0 ≤ Cpref)
    (hentry : (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base Centry)
    (hpref : 9 / 2 * Kpre * (Real.rpow (3 : ℝ) (gam / 2) + 1) ≤
      Real.rpow base Cpref)
    (htransfer : ∀ m : ℕ, 2 * N₀ ≤ m →
      annealedContrast P (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast P q
            (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1)) +
          9 / 2 * Kpre * Real.rpow (3 : ℝ)
            (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ))) :
    ∃ m₀ : ℕ,
      (3 : ℝ) ^ m₀ ≤ Real.rpow base (Centry + (1 + Cpref / (gam / 2))) ∧
        ∀ j : ℕ, annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
          Real.rpow (3 : ℝ) (-(gam / 2) * (j : ℝ)) :=
  exists_annealed_decay_of_hhat_and_transfer
    (by linarith only [hKpre] : (0 : ℝ) ≤ 9 / 2 * Kpre) hgam0 hgam1 hbase
    hCpref hentry hpref (hhat_all_of_hatted_decay hKpre hgam0 hdecay) htransfer

end

end Homogenization.HighContrast.Quenched
