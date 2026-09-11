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
import HCPoly.Provider.Quenched.SmallContrastDropRegroup
import HCPoly.Provider.Quenched.SmallContrastEntryCapsIsotropy
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope
import HCPoly.Provider.Quenched.SmallContrastEntryRateMean
import HCPoly.Provider.Quenched.SmallContrastEntrySupply
import HCPoly.Provider.Quenched.SmallContrastFusionStep
import HCPoly.Provider.Quenched.SmallContrastHatDecay
import HCPoly.Provider.Quenched.SmallContrastHvarFamily
import HCPoly.Provider.Quenched.SmallContrastMeanDropCarrier
import HCPoly.Provider.Quenched.SmallContrastOffsetDropBlock
import HCPoly.Provider.Quenched.SmallContrastOneStepHub
import HCPoly.Provider.Quenched.SmallContrastRealClauses
import HCPoly.Provider.Quenched.SmallContrastRowAtCenters
import HCPoly.Provider.Quenched.SmallContrastSharpLineAtJb
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
# The offset decay read from the origin

The offset iteration concludes at `(n - ns)` in the exponent; the endpoint's
outer composition reads a decay at `n`.  The two differ by one factor
`3 ^ (gam · ns)`, and below the offset the antitone sequence is bounded by its
own initial value, which the same factor covers.

So the passage is an absorption, not an estimate: the shift moves into the
prefactor, and the prefactor is where the endpoint already carries a
polynomially bounded quantity.
-/

namespace Homogenization.HighContrast.Quenched

noncomputable section

/-- The natural-power form of the geometric factor is its real power. -/
theorem three_rpow_neg_pow_eq (gam : ℝ) (k : ℕ) :
    ((3 : ℝ) ^ (-gam)) ^ k = (3 : ℝ) ^ (-gam * (k : ℝ)) := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-gam)) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- **The offset decay, read from the origin.**  The offset joins the
prefactor. -/
theorem hatted_decay_of_offset_decay {F : ℕ → ℝ} {Kpre gam : ℝ} {ns : ℕ}
    (hgam0 : 0 < gam) (hKpre0 : 0 ≤ Kpre)
    (hFnn : ∀ n, 0 ≤ F n)
    (hFmono : ∀ m n : ℕ, m ≤ n → F n ≤ F m)
    (hoff : ∀ n : ℕ, ns ≤ n → F n ≤ Kpre * ((3 : ℝ) ^ (-gam)) ^ (n - ns)) :
    ∀ n : ℕ, F n ≤ ((Kpre + F 0) * (3 : ℝ) ^ (gam * (ns : ℝ))) *
      (3 : ℝ) ^ (-gam * (n : ℝ)) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hshift0 : (0 : ℝ) < (3 : ℝ) ^ (gam * (ns : ℝ)) :=
    Real.rpow_pos_of_pos h30 _
  have hF00 : (0 : ℝ) ≤ F 0 := hFnn 0
  have hsum0 : (0 : ℝ) ≤ Kpre + F 0 := by linarith only [hKpre0, hF00]
  intro n
  have hn0 : (0 : ℝ) < (3 : ℝ) ^ (-gam * (n : ℝ)) :=
    Real.rpow_pos_of_pos h30 _
  rcases le_or_gt ns n with hle | hlt
  · -- past the offset: the offset joins the prefactor
    have hcast : ((n - ns : ℕ) : ℝ) = (n : ℝ) - (ns : ℝ) := by
      have : ns ≤ n := hle
      push_cast [Nat.cast_sub this]
      ring
    have hpow : ((3 : ℝ) ^ (-gam)) ^ (n - ns) =
        (3 : ℝ) ^ (-gam * (n : ℝ)) * (3 : ℝ) ^ (gam * (ns : ℝ)) := by
      rw [three_rpow_neg_pow_eq, hcast, ← Real.rpow_add h30]
      congr 1
      ring
    have hbase := hoff n hle
    rw [hpow] at hbase
    have hstep : Kpre * ((3 : ℝ) ^ (-gam * (n : ℝ)) *
          (3 : ℝ) ^ (gam * (ns : ℝ))) ≤
        (Kpre + F 0) * (3 : ℝ) ^ (gam * (ns : ℝ)) *
          (3 : ℝ) ^ (-gam * (n : ℝ)) := by
      have hmul : (0 : ℝ) ≤ (3 : ℝ) ^ (-gam * (n : ℝ)) *
          (3 : ℝ) ^ (gam * (ns : ℝ)) :=
        mul_nonneg hn0.le hshift0.le
      have hle' : Kpre ≤ Kpre + F 0 := by linarith only [hF00]
      have h := mul_le_mul_of_nonneg_right hle' hmul
      have hcomm : (Kpre + F 0) * ((3 : ℝ) ^ (-gam * (n : ℝ)) *
          (3 : ℝ) ^ (gam * (ns : ℝ))) =
          (Kpre + F 0) * (3 : ℝ) ^ (gam * (ns : ℝ)) *
            (3 : ℝ) ^ (-gam * (n : ℝ)) := by ring
      rw [hcomm] at h
      exact le_trans h (le_of_eq rfl)
    exact le_trans hbase hstep
  · -- below the offset: the initial value is covered by the same factor
    have hnle : (n : ℝ) ≤ (ns : ℝ) := by
      have : n ≤ ns := le_of_lt hlt
      exact_mod_cast this
    have hexp : -gam * (ns : ℝ) ≤ -gam * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hnle hgam0.le
      linarith only [this]
    have hmono : (3 : ℝ) ^ (-gam * (ns : ℝ)) ≤ (3 : ℝ) ^ (-gam * (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hcancel : (3 : ℝ) ^ (gam * (ns : ℝ)) * (3 : ℝ) ^ (-gam * (ns : ℝ)) =
        1 := by
      rw [← Real.rpow_add h30]
      have hzero : gam * (ns : ℝ) + -gam * (ns : ℝ) = 0 := by ring
      rw [hzero, Real.rpow_zero]
    have hstep : (Kpre + F 0) * (3 : ℝ) ^ (gam * (ns : ℝ)) *
        (3 : ℝ) ^ (-gam * (ns : ℝ)) ≤
        (Kpre + F 0) * (3 : ℝ) ^ (gam * (ns : ℝ)) *
          (3 : ℝ) ^ (-gam * (n : ℝ)) := by
      refine mul_le_mul_of_nonneg_left hmono ?_
      exact mul_nonneg hsum0 hshift0.le
    have hid : (Kpre + F 0) * (3 : ℝ) ^ (gam * (ns : ℝ)) *
        (3 : ℝ) ^ (-gam * (ns : ℝ)) = Kpre + F 0 := by
      rw [mul_assoc, hcancel, mul_one]
    rw [hid] at hstep
    have hFle : F n ≤ F 0 := hFmono 0 n (Nat.zero_le n)
    linarith only [hFle, hstep, hKpre0]

end

end Homogenization.HighContrast.Quenched
