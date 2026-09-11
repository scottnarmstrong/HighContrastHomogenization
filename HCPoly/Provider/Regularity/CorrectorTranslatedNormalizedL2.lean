/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CorrectorNormalizedL2Bridge
import HCPoly.Provider.Regularity.LocalGradientTranslation

/-!
# Normalized L2 control under translation

Translation carries a smaller set into a larger one without changing the
unnormalized integral.  For volume-normalized `L²`, the only cost is therefore
the square root of the volume ratio.  This fact is specialized to the centered
cube exhaustion and its canonical translation-depth shift.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- If translation by `z` carries `U` into `V`, the normalized `L²` norm of
the translated function on `U` costs at most the square root of the volume
ratio between `V` and `U`. -/
theorem normalizedL2Norm_translate_le_volumeRatio
    {d : ℕ} {U V : Set (Vec d)} (z : Vec d)
    (hUV : ∀ x ∈ U, x + z ∈ V)
    (hVmeas : MeasurableSet V)
    (hUzero : volume U ≠ 0) (hUtop : volume U ≠ ⊤)
    (hVzero : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    (f : Vec d → ℝ) :
    normalizedL2Norm U (fun x => f (x + z)) ≤
      (volume V / volume U) ^ (1 / 2 : ℝ) *
        normalizedL2Norm V f := by
  let IU : ℝ≥0∞ :=
    ∫⁻ x in U, ENNReal.ofReal ((f (x + z)) ^ 2) ∂volume
  let IV : ℝ≥0∞ :=
    ∫⁻ x in V, ENNReal.ofReal ((f x) ^ 2) ∂volume
  have hpreimage : U ⊆ (fun x : Vec d => x + z) ⁻¹' V :=
    fun x hx => hUV x hx
  have hI : IU ≤ IV := by
    calc
      IU ≤ ∫⁻ x in (fun x : Vec d => x + z) ⁻¹' V,
          ENNReal.ofReal ((f (x + z)) ^ 2) ∂volume := by
        dsimp only [IU]
        exact lintegral_mono'
          (Measure.restrict_mono_set volume hpreimage) le_rfl
      _ = IV := by
        dsimp only [IV]
        let hpreserving :=
          (measurePreserving_add_right (volume : Measure (Vec d)) z).restrict_preimage
            hVmeas
        exact hpreserving.lintegral_comp_emb
          (Homeomorph.addRight z).measurableEmbedding
          (fun y => ENNReal.ofReal ((f y) ^ 2))
  have hbase : IU / volume U ≤
      (volume V / volume U) * (IV / volume V) := by
    rw [ENNReal.div_le_iff hUzero hUtop]
    have hcancel :
        (volume V / volume U) * (IV / volume V) * volume U = IV := by
      calc
        (volume V / volume U) * (IV / volume V) * volume U =
            (volume V / volume U * volume U) * (IV / volume V) := by
              ac_rfl
        _ = volume V * (IV / volume V) := by
          rw [ENNReal.div_mul_cancel hUzero hUtop]
        _ = IV := ENNReal.mul_div_cancel hVzero hVtop
    exact hI.trans_eq hcancel.symm
  have hrpow := ENNReal.rpow_le_rpow hbase
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _
    (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hrpow
  simpa only [normalizedL2Norm, eVolumeAverage, IU, IV] using hrpow

private theorem volume_localGradientCube_ne_zero (d n : ℕ) :
    volume (localGradientCube d n) ≠ 0 := by
  intro hzero
  have hvolume := volume_openCubeSet_toReal (originCube d (n : ℤ))
  rw [show openCubeSet (originCube d (n : ℤ)) =
      localGradientCube d n by rfl, hzero] at hvolume
  simp only [ENNReal.toReal_zero] at hvolume
  exact (cubeVolume_pos (originCube d (n : ℤ))).ne' hvolume.symm

/-- Canonical exhaustion-cube specialization: translating the `n`th cube is
controlled by the cube shifted by `translationDepth z`. -/
theorem normalizedL2Norm_translate_localGradientCube_le
    {d : ℕ} (z : Vec d) (n : ℕ) (f : Vec d → ℝ) :
    normalizedL2Norm (localGradientCube d n) (fun x => f (x + z)) ≤
      (volume (localGradientCube d (n + translationDepth z)) /
          volume (localGradientCube d n)) ^ (1 / 2 : ℝ) *
        normalizedL2Norm (localGradientCube d (n + translationDepth z)) f := by
  apply normalizedL2Norm_translate_le_volumeRatio z
    (fun x hx => add_mem_localGradientCube z n hx)
  · exact (isOpen_openCubeSet
      (originCube d ((n + translationDepth z : ℕ) : ℤ))).measurableSet
  · exact volume_localGradientCube_ne_zero d n
  · exact (volume_openCubeSet_lt_top (originCube d (n : ℤ))).ne
  · exact volume_localGradientCube_ne_zero d (n + translationDepth z)
  · exact (volume_openCubeSet_lt_top
      (originCube d ((n + translationDepth z : ℕ) : ℤ))).ne

end

end HighContrast
end Homogenization
