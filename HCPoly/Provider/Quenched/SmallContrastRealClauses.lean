/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.SmallContrastAdjointMirrors
import HCPoly.Provider.Quenched.SmallContrastAnnealedEnvelope
import HCPoly.Provider.Quenched.SmallContrastAverageDrops
import HCPoly.Provider.Quenched.SmallContrastCenteringCap
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope
import HCPoly.Provider.Quenched.SmallContrastLineProducer
import HCPoly.Provider.Quenched.SmallContrastRowAtCenters
import HCPoly.Provider.Quenched.SmallContrastWeakCap
import HCPoly.Provider.Quenched.SmallContrastWeakValue
import HCPoly.Provider.Response.DiagonalWeakNormAdjointAlgebra
import HCPoly.Provider.Response.PreYoungFixedGridCells
import HCPoly.Provider.Response.ProfileRowOscillationSum
import HCPoly.Provider.Response.ProfileRowSchur
import HCPoly.Provider.Response.ProfileRowSkewCarriers

/-!
# Three structural clauses for the generation-indexed estimate

This file supplies three hypotheses of `exists_one_step_with_slots_of_block_at_level_conv_split` uniformly
in the generation.

* **The source clause is a threshold, and thresholds are monotone.**  Its
  exponent `(t - Hw) + (Gacc + 1) - sKw` is increasing in `n`, so assuming it at
  the delayed start `ns` gives it at every later generation by
  `zpow_le_zpow_right₀`.

* **The bootstrap floor is a hypothesis of Proposition 4.2, not a lemma.**
  `account_smallness_pack` *takes* `∀ k, l ≤ k → k ≤ t → hatExcessAt P q k ≤ δ`
  and does not produce it.  Stated over the whole ray `l ≤ k`, this hypothesis
  restricts to every `t = N₀ + n`.

* **The Schur data is structural.**  `schur_pack_at_terminal` needs only that
  `adaptedMean P q t` is symmetric and positive definite, and both hold at every
  scale (`isSymmetricBlockMat_adaptedMean`,
  `blockPosDef_adaptedMean_of_isRoundedGrid`).

Thus one clause is monotonicity of a threshold, one is a standing floor
hypothesis, and one follows from the Schur structure.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Clause 1: the source threshold -/

/-! ## Clause 2: the bootstrap floor -/

/-! ## Clause 3: the Schur data -/

/-- **The Schur data exists at every generation**, from the structural facts
about the adapted mean alone. -/
theorem schur_data_at_generation [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k) (t : ℤ) :
    ∃ S0 SStar0 K0 : Mat d, S0.PosDef ∧ SStar0.PosDef ∧
      toFullBlockMat (adaptedMean P q t) = schurBlock S0 SStar0 K0 ∧
      (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) = hatExcessAt P q t :=
  schur_pack_at_terminal (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
    (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq t (hfin t))

/-! ## The `eps = 0` case split -/

end

end Homogenization.HighContrast.Quenched
