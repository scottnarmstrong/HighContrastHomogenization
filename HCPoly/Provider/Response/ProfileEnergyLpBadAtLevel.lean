/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileEnergyLp

/-!
# The bad optimizer energy at a released split level

The bad branch of the optimizer-energy estimate, with the bad-event level a
parameter.  The fixed-level statements are these at `lev = 1`: the carrier
`profileBadEnergyAt` and the majorant `profileBadMajorantAt` are both the
fixed-level objects on the nose there, so nothing is lost by stating the
estimate here and specializing.

The proofs are the fixed-level ones with the complete-maximum comparison read
at the released level.  Both use the released pointwise energy bounds, whose
level hypothesis is the printed range's left endpoint `1 ≤ lev`.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The generic bad-branch estimate at a released level.**  The
complete-maximum comparison, the energy's pathwise bound on the bad event and
the total-profile moment, all read at the level `lev`. -/
theorem profileBadEnergyAt_le_of_complete_maximum
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q h beta lev : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    {M W : CoeffSpace d → ℝ≥0∞} (hM : AEMeasurable M P)
    (hW : AEMeasurable W P)
    (hpoint : ∀ a, M a ≤ W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm M (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h)
    {energy : CoeffSpace d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ a, M a ≠ ⊤ → ENNReal.ofReal lev < M a →
      energy a ≤ C * Real.sqrt (M a).toReal) :
    profileBadEnergyAt P (ENNReal.ofReal lev) M energy ≤
      ENNReal.ofReal (C * profileBadMajorantAt Q h beta lev) := by
  let bad : Set (CoeffSpace d) := {a | ENNReal.ofReal lev < M a}
  have hfinite := ae_ne_top_of_eLpNorm_le_ofReal
    (lt_trans (by norm_num) hQ) hM hnorm
  have hbadNull : NullMeasurableSet bad P :=
    nullMeasurableSet_lt aemeasurable_const hM
  have hbadM : AEStronglyMeasurable (bad.indicator M) P :=
    (hM.indicator₀ hbadNull).aestronglyMeasurable
  have hmono : eLpNorm (bad.indicator fun a =>
      M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (energy a)) 2 P ≤
      eLpNorm (fun a => ENNReal.ofReal C * bad.indicator M a) 2 P := by
    apply eLpNorm_mono_enorm_ae
    filter_upwards [hfinite] with a ha
    by_cases habad : a ∈ bad
    · simp only [Set.indicator_of_mem habad, enorm_eq_self]
      exact rpow_half_mul_ofReal_le_of_le_sqrt_toReal ha hC
        (henergy a ha habad)
    · simp only [Set.indicator_of_notMem habad, mul_zero, enorm_zero]
      exact le_rfl
  have hmaximum := eLpNorm_indicator_gt_level_le_profileBadMajorantAt
    (lev := lev) P hQ hh hbeta hM hW hpoint hnorm hmoment
  calc
    profileBadEnergyAt P (ENNReal.ofReal lev) M energy ≤
        eLpNorm (fun a => ENNReal.ofReal C * bad.indicator M a) 2 P := hmono
    _ ≤ ENNReal.ofReal C * eLpNorm (bad.indicator M) 2 P :=
      eLpNorm_ofReal_mul_le hbadM C 2
    _ ≤ ENNReal.ofReal C *
        ENNReal.ofReal (profileBadMajorantAt Q h beta lev) :=
      mul_le_mul_of_nonneg_left (by simpa only [bad] using hmaximum) (zero_le _)
    _ = ENNReal.ofReal (C * profileBadMajorantAt Q h beta lev) := by
      rw [← ENNReal.ofReal_mul hC]

/-- The primal bad optimizer energy at a released level. -/
theorem profileBadEnergyAt_diagonalWeakEnergy_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q h beta lev rho : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    (hlev : 1 ≤ lev)
    {q : Mat d} (hq : q.PosDef) {t : ℤ} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {W : CoeffSpace d → ℝ≥0∞} (hW : AEMeasurable W P)
    (hpoint : ∀ a, diagonalWeakMaximum rho q t E a ≤
      W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm (diagonalWeakMaximum rho q t E)
      (ENNReal.ofReal Q) P ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h)
    (p r : Vec d) :
    profileBadEnergyAt P (ENNReal.ofReal lev)
      (diagonalWeakMaximum rho q t E)
      (fun a => diagonalWeakEnergy hq t a p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        profileEnergyLoad (diagonalWeakLoadMinus E p r) p r *
        profileBadMajorantAt Q h beta lev) := by
  let C := Real.sqrt 2 *
    profileEnergyLoad (diagonalWeakLoadMinus E p r) p r
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _)
    (profileEnergyLoad_nonneg (diagonalWeakLoadMinus E p r) p r)
  apply profileBadEnergyAt_le_of_complete_maximum hQ hh hbeta
    (aemeasurable_diagonalWeakMaximum hq hE hEpd) hW hpoint hnorm hmoment hC
  intro a hfinite hbad
  have hbound := diagonalWeakEnergy_le_sqrt_two_mul_bad_at_level
    hq hE hEpd p r hlev hfinite hbad
  change diagonalWeakEnergy hq t a p r ≤
    C * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
  calc
    diagonalWeakEnergy hq t a p r ≤
        Real.sqrt 2 * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
          profileEnergyLoad (diagonalWeakLoadMinus E p r) p r := hbound
    _ = C * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal := by
      dsimp only [C]
      ring

/-- The adjoint bad optimizer energy at a released level. -/
theorem profileBadEnergyAt_diagonalWeakAdjointEnergy_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q h beta lev rho : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    (hlev : 1 ≤ lev)
    {q : Mat d} (hq : q.PosDef) {t : ℤ} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {W : CoeffSpace d → ℝ≥0∞} (hW : AEMeasurable W P)
    (hpoint : ∀ a, diagonalWeakMaximum rho q t E a ≤
      W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm (diagonalWeakMaximum rho q t E)
      (ENNReal.ofReal Q) P ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h)
    (p r : Vec d) :
    profileBadEnergyAt P (ENNReal.ofReal lev)
      (diagonalWeakMaximum rho q t E)
      (fun a => diagonalWeakAdjointEnergy hq t a p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        profileEnergyLoad (diagonalWeakLoadPlus E p r) p r *
        profileBadMajorantAt Q h beta lev) := by
  let C := Real.sqrt 2 *
    profileEnergyLoad (diagonalWeakLoadPlus E p r) p r
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _)
    (profileEnergyLoad_nonneg (diagonalWeakLoadPlus E p r) p r)
  apply profileBadEnergyAt_le_of_complete_maximum hQ hh hbeta
    (aemeasurable_diagonalWeakMaximum hq hE hEpd) hW hpoint hnorm hmoment hC
  intro a hfinite hbad
  have hbound := diagonalWeakAdjointEnergy_le_sqrt_two_mul_bad_at_level
    hq hE hEpd p r hlev hfinite hbad
  change diagonalWeakAdjointEnergy hq t a p r ≤
    C * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
  calc
    diagonalWeakAdjointEnergy hq t a p r ≤
        Real.sqrt 2 * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
          profileEnergyLoad (diagonalWeakLoadPlus E p r) p r := hbound
    _ = C * Real.sqrt (diagonalWeakMaximum rho q t E a).toReal := by
      dsimp only [C]
      ring

end

end Homogenization.HighContrast.Response
