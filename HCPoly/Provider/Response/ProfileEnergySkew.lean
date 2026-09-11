/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileEnergyLp
import HCPoly.Provider.Response.ConstantSkewProfiles

/-!
# Optimizer-energy bounds after skew recentering

The coefficient sample and its deterministic reference are transformed by the
same constant shear.  The maximum is therefore unchanged, while the primal and
coefficient-transpose optimizer energies retain their independent loads.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The bad-event primal energy estimate in the recentered coordinates. -/
theorem profileBadEnergy_subSkew_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q h beta rho : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    {q : Mat d} (hq : q.PosDef) {t : ℤ} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {W : CoeffSpace d → ℝ≥0∞} (hW : AEMeasurable W P)
    (hpoint : ∀ a, diagonalWeakMaximum rho q t E a ≤
      W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm (diagonalWeakMaximum rho q t E)
      (ENNReal.ofReal Q) P ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    profileBadEnergy P
        (fun a ↦ diagonalWeakMaximum rho q t (skewBlockCongr g E)
          (a.subSkew g hg))
        (fun a ↦ diagonalWeakEnergy hq t (a.subSkew g hg) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        profileEnergyLoad
          (diagonalWeakLoadMinus (skewBlockCongr g E) p r) p r *
        profileBadMajorant Q h beta) := by
  let M : CoeffSpace d → ℝ≥0∞ := fun a ↦
    diagonalWeakMaximum rho q t (skewBlockCongr g E) (a.subSkew g hg)
  let energy : CoeffSpace d → ℝ := fun a ↦
    diagonalWeakEnergy hq t (a.subSkew g hg) p r
  let C : ℝ := Real.sqrt 2 *
    profileEnergyLoad (diagonalWeakLoadMinus (skewBlockCongr g E) p r) p r
  have hM_eq : M = diagonalWeakMaximum rho q t E := by
    funext a
    exact diagonalWeakMaximum_subSkew hq rho t E a g hg
  have hM : AEMeasurable M P := by
    rw [hM_eq]
    exact aemeasurable_diagonalWeakMaximum hq hE hEpd
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _)
    (profileEnergyLoad_nonneg
      (diagonalWeakLoadMinus (skewBlockCongr g E) p r) p r)
  apply profileBadEnergy_le_of_complete_maximum hQ hh hbeta hM hW
    (by simpa only [hM_eq] using hpoint)
    (by simpa only [hM_eq] using hnorm) hmoment hC
  intro a hfinite hbad
  have hraw := diagonalWeakEnergy_le_sqrt_two_mul_bad hq
    (isSymmetricBlockMat_skewBlockCongr hE)
    (blockPosDef_skewBlockCongr hEpd) p r hfinite hbad
  change diagonalWeakEnergy hq t (a.subSkew g hg) p r ≤
    C * Real.sqrt (M a).toReal
  calc
    diagonalWeakEnergy hq t (a.subSkew g hg) p r ≤
        Real.sqrt 2 * Real.sqrt (M a).toReal *
          profileEnergyLoad
            (diagonalWeakLoadMinus (skewBlockCongr g E) p r) p r := hraw
    _ = C * Real.sqrt (M a).toReal := by
      dsimp only [C]
      ring

/-- The bad-event coefficient-transpose energy estimate in the recentered
coordinates. -/
theorem profileBadAdjointEnergy_subSkew_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q h beta rho : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    {q : Mat d} (hq : q.PosDef) {t : ℤ} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {W : CoeffSpace d → ℝ≥0∞} (hW : AEMeasurable W P)
    (hpoint : ∀ a, diagonalWeakMaximum rho q t E a ≤
      W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm (diagonalWeakMaximum rho q t E)
      (ENNReal.ofReal Q) P ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    profileBadEnergy P
        (fun a ↦ diagonalWeakMaximum rho q t (skewBlockCongr g E)
          (a.subSkew g hg))
        (fun a ↦ diagonalWeakAdjointEnergy hq t (a.subSkew g hg) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        profileEnergyLoad
          (diagonalWeakLoadPlus (skewBlockCongr g E) p r) p r *
        profileBadMajorant Q h beta) := by
  let M : CoeffSpace d → ℝ≥0∞ := fun a ↦
    diagonalWeakMaximum rho q t (skewBlockCongr g E) (a.subSkew g hg)
  let energy : CoeffSpace d → ℝ := fun a ↦
    diagonalWeakAdjointEnergy hq t (a.subSkew g hg) p r
  let C : ℝ := Real.sqrt 2 *
    profileEnergyLoad (diagonalWeakLoadPlus (skewBlockCongr g E) p r) p r
  have hM_eq : M = diagonalWeakMaximum rho q t E := by
    funext a
    exact diagonalWeakMaximum_subSkew hq rho t E a g hg
  have hM : AEMeasurable M P := by
    rw [hM_eq]
    exact aemeasurable_diagonalWeakMaximum hq hE hEpd
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _)
    (profileEnergyLoad_nonneg
      (diagonalWeakLoadPlus (skewBlockCongr g E) p r) p r)
  apply profileBadEnergy_le_of_complete_maximum hQ hh hbeta hM hW
    (by simpa only [hM_eq] using hpoint)
    (by simpa only [hM_eq] using hnorm) hmoment hC
  intro a hfinite hbad
  have hraw := diagonalWeakAdjointEnergy_le_sqrt_two_mul_bad hq
    (isSymmetricBlockMat_skewBlockCongr hE)
    (blockPosDef_skewBlockCongr hEpd) p r hfinite hbad
  change diagonalWeakAdjointEnergy hq t (a.subSkew g hg) p r ≤
    C * Real.sqrt (M a).toReal
  calc
    diagonalWeakAdjointEnergy hq t (a.subSkew g hg) p r ≤
        Real.sqrt 2 * Real.sqrt (M a).toReal *
          profileEnergyLoad
            (diagonalWeakLoadPlus (skewBlockCongr g E) p r) p r := hraw
    _ = C * Real.sqrt (M a).toReal := by
      dsimp only [C]
      ring

/-- The good-event primal energy estimate in the recentered coordinates. -/
theorem profileGoodEnergy_subSkew_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {alpha rho : ℝ} {H : ℕ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    profileGoodEnergy P alpha H
        (fun a ↦ diagonalWeakMaximum rho q t (skewBlockCongr g E)
          (a.subSkew g hg))
        (fun a ↦ diagonalWeakEnergy hq t (a.subSkew g hg) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 * (3 : ℝ) ^ (-alpha * (H : ℝ)) *
        profileEnergyLoad
          (diagonalWeakLoadMinus (skewBlockCongr g E) p r) p r) := by
  have hmain := profileGoodEnergy_le_of_pointwise
    (P := P) (alpha := alpha) (H := H)
    (M := fun a ↦ diagonalWeakMaximum rho q t (skewBlockCongr g E)
      (a.subSkew g hg))
    (energy := fun a ↦ diagonalWeakEnergy hq t (a.subSkew g hg) p r)
    (fun a hgood ↦ diagonalWeakEnergy_le_sqrt_two_mul_good hq
      (isSymmetricBlockMat_skewBlockCongr hE)
      (blockPosDef_skewBlockCongr hEpd) p r hgood)
  exact hmain.trans_eq (congrArg ENNReal.ofReal (by
    ring))

/-- The good-event coefficient-transpose energy estimate in the recentered
coordinates. -/
theorem profileGoodAdjointEnergy_subSkew_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {alpha rho : ℝ} {H : ℕ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    profileGoodEnergy P alpha H
        (fun a ↦ diagonalWeakMaximum rho q t (skewBlockCongr g E)
          (a.subSkew g hg))
        (fun a ↦ diagonalWeakAdjointEnergy hq t (a.subSkew g hg) p r) ≤
      ENNReal.ofReal (Real.sqrt 2 * (3 : ℝ) ^ (-alpha * (H : ℝ)) *
        profileEnergyLoad
          (diagonalWeakLoadPlus (skewBlockCongr g E) p r) p r) := by
  have hmain := profileGoodEnergy_le_of_pointwise
    (P := P) (alpha := alpha) (H := H)
    (M := fun a ↦ diagonalWeakMaximum rho q t (skewBlockCongr g E)
      (a.subSkew g hg))
    (energy := fun a ↦ diagonalWeakAdjointEnergy hq t
      (a.subSkew g hg) p r)
    (fun a hgood ↦ diagonalWeakAdjointEnergy_le_sqrt_two_mul_good hq
      (isSymmetricBlockMat_skewBlockCongr hE)
      (blockPosDef_skewBlockCongr hEpd) p r hgood)
  exact hmain.trans_eq (congrArg ENNReal.ofReal (by
    ring))

end

end Homogenization.HighContrast.Response
