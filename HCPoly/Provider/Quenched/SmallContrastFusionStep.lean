/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.Prop42Tilt.CorrectedTiltAdapter
import HCPoly.Provider.Quenched.SmallContrastBootstrapTilt
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope
import HCPoly.Provider.Quenched.SmallContrastEntryEstimates
import HCPoly.Provider.Quenched.SmallContrastTerminalComparability

/-!
# The fusion's `∀ n` binder body

the corresponding argument step 3.  Inside the fusion's `∀ n ≥ n_s` binder, the account's hatted
one-step conclusion at the generation `t = N₀ + n` has to become one line of
the drop-history recursion for the sequence `F j = hatExcess P q N₀ j`.  This
file is that line, isolated as a lemma so the outer assembly can apply it
without carrying the algebra.

The identifications are definitional: `hatExcess P q N₀ n` *is*
`d(Θ̂_{N₀+n} − 1)`, and the account's lagged scale `s = t − H` *is*
`N₀ + (n − H)`, so `one_step_to_scalar_step_isotropy` (the scalar conversion) yields directly in the
shape `per_generation_hrec_at_recursionAlpha_sharp_at_jb_src` consumes.  Nothing else happens
here; the three coefficients are `dropCoefficient`, `quadCoefficient` and
`weakCoefficient` of the corresponding argument.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

theorem weakCoefficient_nonneg (d : ℕ) {Cpre : ℝ} (hCpre : 0 ≤ Cpre) :
    0 ≤ weakCoefficient d Cpre := by
  rw [weakCoefficient]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have : (0 : ℝ) ≤ 4 * Cpre := by linarith only [hCpre]
  exact mul_nonneg this hd0

theorem dropCoefficient_nonneg (d : ℕ) {Cpre eta : ℝ} (hCpre : 0 ≤ Cpre)
    (heta : 0 < eta) : 0 ≤ dropCoefficient d Cpre eta := by
  rw [dropCoefficient]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h1 : (0 : ℝ) ≤ 64 * Cpre * (d : ℝ) := by
    have : (0 : ℝ) ≤ 64 * Cpre := by linarith only [hCpre]
    exact mul_nonneg this hd0
  have h2 : (0 : ℝ) ≤ 3 / 2 + 1 / (4 * eta) := by
    have : (0 : ℝ) < 1 / (4 * eta) := by positivity
    linarith only [this]
  exact mul_nonneg h1 h2

end

end Homogenization.HighContrast.Quenched
