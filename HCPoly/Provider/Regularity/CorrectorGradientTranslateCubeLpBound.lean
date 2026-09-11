/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CorrectorGradientCubeIntegralTranslationStability
import HCPoly.Provider.Regularity.CorrectorTranslatedNormalizedL2

/-!
# Normalized `L²` bounds for translated corrector gradients

Translation embeds the `n`th centered cube into the cube shifted by
`translationDepth`.  This gives the exact square-root volume-ratio bound for
vector-valued normalized `L²` norms and its canonical corrector specialization.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

/-- Taking the pointwise norm does not change `cubeLpNorm`. -/
theorem cubeLpNorm_norm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ENNReal) (F : Vec d → E) :
    cubeLpNorm Q p (fun x ↦ ‖F x‖) = cubeLpNorm Q p F := by
  unfold cubeLpNorm
  rw [eLpNorm_norm]

private theorem volume_localGradientCube_ne_zero_for_translateLp
    (d n : ℕ) : volume (localGradientCube d n) ≠ 0 := by
  intro hzero
  have hvolume := volume_openCubeSet_toReal (originCube d (n : ℤ))
  rw [show openCubeSet (originCube d (n : ℤ)) = localGradientCube d n by rfl,
    hzero] at hvolume
  simp only [ENNReal.toReal_zero] at hvolume
  exact (cubeVolume_pos (originCube d (n : ℤ))).ne' hvolume.symm

/-- Vector-valued normalized `L²` translation costs exactly the square root
of the containing-to-contained cube volume ratio. -/
theorem cubeLpNorm_translate_localGradientCube_le_volumeRatio
    {d : ℕ} (t : Vec d) (n : ℕ) (F : Vec d → Vec d)
    (hF : MemLp F (2 : ENNReal)
      (normalizedCubeMeasure (originCube d ((n + translationDepth t : ℕ) : ℤ))))
    (hFt : MemLp (fun x ↦ F (x + t)) (2 : ENNReal)
      (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal) (fun x ↦ F (x + t)) ≤
      ((volume (localGradientCube d (n + translationDepth t)) /
          volume (localGradientCube d n)) ^ (1 / 2 : ℝ)).toReal *
        cubeLpNorm (originCube d ((n + translationDepth t : ℕ) : ℤ))
          (2 : ENNReal) F := by
  have hnorm := normalizedL2Norm_translate_localGradientCube_le
    t n (fun x ↦ ‖F x‖)
  change normalizedL2Norm (openCubeSet (originCube d (n : ℤ)))
      (fun x ↦ ‖F (x + t)‖) ≤
    (volume (localGradientCube d (n + translationDepth t)) /
        volume (localGradientCube d n)) ^ (1 / 2 : ℝ) *
      normalizedL2Norm
        (openCubeSet (originCube d ((n + translationDepth t : ℕ) : ℤ)))
        (fun x ↦ ‖F x‖) at hnorm
  rw [normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
      (originCube d (n : ℤ)) (fun x ↦ ‖F (x + t)‖) (by
        simpa only [Function.comp_apply] using hFt.norm),
    normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
      (originCube d ((n + translationDepth t : ℕ) : ℤ))
      (fun x ↦ ‖F x‖) hF.norm] at hnorm
  let R : ENNReal :=
    (volume (localGradientCube d (n + translationDepth t)) /
      volume (localGradientCube d n)) ^ (1 / 2 : ℝ)
  have hratioTop :
      volume (localGradientCube d (n + translationDepth t)) /
          volume (localGradientCube d n) ≠ ⊤ :=
    ENNReal.div_ne_top
      (volume_openCubeSet_lt_top
        (originCube d ((n + translationDepth t : ℕ) : ℤ))).ne
      (volume_localGradientCube_ne_zero_for_translateLp d n)
  have hRTop : R ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hratioTop
  have hleftTop :
      ENNReal.ofReal
        (cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal)
          (fun x ↦ ‖F (x + t)‖)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrightTop :
      R * ENNReal.ofReal
        (cubeLpNorm (originCube d ((n + translationDepth t : ℕ) : ℤ))
          (2 : ENNReal) (fun x ↦ ‖F x‖)) ≠ ⊤ :=
    ENNReal.mul_ne_top hRTop ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).mpr (by
    simpa only [R] using hnorm)
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (cubeLpNorm_nonneg _ _ _),
    ENNReal.toReal_ofReal (cubeLpNorm_nonneg _ _ _),
    cubeLpNorm_norm, cubeLpNorm_norm] at hreal
  exact hreal

/-- Canonical corrector specialization of the translated volume-ratio bound. -/
theorem NormalizedLocalH1Carrier.cubeLpNorm_globalGradient_translate_le_volumeRatio
    {d : ℕ} (Phi : NormalizedLocalH1Carrier d) (t : Vec d) (n : ℕ) :
    cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal)
        (fun x ↦ Phi.globalGradientRepresentative (x + t)) ≤
      ((volume (localGradientCube d (n + translationDepth t)) /
          volume (localGradientCube d n)) ^ (1 / 2 : ℝ)).toReal *
        cubeLpNorm (originCube d ((n + translationDepth t : ℕ) : ℤ))
          (2 : ENNReal) Phi.globalGradientRepresentative := by
  exact cubeLpNorm_translate_localGradientCube_le_volumeRatio t n
    Phi.globalGradientRepresentative
    (Phi.memLp_globalGradientRepresentative_normalizedCubeMeasure
      (n + translationDepth t))
    (Phi.memLp_globalGradientRepresentative_translate_normalizedCubeMeasure t n)

/-- A uniform unshifted corrector-gradient bound controls every translated
cube with the explicit per-scale volume-ratio factor. -/
theorem NormalizedLocalH1Carrier.cubeLpNorm_globalGradient_translate_le_volumeRatio_mul
    {d : ℕ} (Phi : NormalizedLocalH1Carrier d) (t : Vec d) (M : ℝ)
    (hM : ∀ q : ℕ,
      cubeLpNorm (originCube d (q : ℤ)) (2 : ENNReal)
        Phi.globalGradientRepresentative ≤ M)
    (n : ℕ) :
    cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal)
        (fun x ↦ Phi.globalGradientRepresentative (x + t)) ≤
      ((volume (localGradientCube d (n + translationDepth t)) /
          volume (localGradientCube d n)) ^ (1 / 2 : ℝ)).toReal * M := by
  exact (Phi.cubeLpNorm_globalGradient_translate_le_volumeRatio t n).trans
    (mul_le_mul_of_nonneg_left (hM (n + translationDepth t)) ENNReal.toReal_nonneg)

end

end HighContrast
end Homogenization
