/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.LocalGradientTranslation
import Homogenization.Geometry.CubeMeasure

/-!
# Boundary geometry for fixed translations of centered cubes

A fixed translation changes a large centered cube only inside a boundary
layer whose relative thickness tends to zero.  This file isolates the purely
geometric part of that comparison.
-/

namespace Homogenization
namespace HighContrast

open Filter MeasureTheory Set

noncomputable section

/-- A normalized boundary thickness which is strictly larger than every
coordinate displacement of `t`.  The extra unit gives strict containment in
the open translated cube. -/
def normalizedTranslationBoundaryThickness {d : ℕ}
    (t : Vec d) (n : ℕ) : ℝ :=
  (‖t‖ + 1) / cubeScaleFactor (originCube d (n : ℤ))

theorem normalizedTranslationBoundaryThickness_pos {d : ℕ}
    (t : Vec d) (n : ℕ) :
    0 < normalizedTranslationBoundaryThickness t n := by
  apply div_pos
  · linarith only [norm_nonneg t]
  · exact zpow_pos (by norm_num : (0 : ℝ) < 3) _

/-- The normalized thickness of a fixed translation tends to zero along the
centered triadic exhaustion. -/
theorem tendsto_normalizedTranslationBoundaryThickness_zero {d : ℕ}
    (t : Vec d) :
    Tendsto (normalizedTranslationBoundaryThickness t) atTop (nhds 0) := by
  unfold normalizedTranslationBoundaryThickness
  simpa only [cubeScaleFactor_originCube, zpow_natCast] using
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3))

/-- Eventually the translation boundary layer occupies at most half the
normalized cube width. -/
theorem eventually_normalizedTranslationBoundaryThickness_le_half {d : ℕ}
    (t : Vec d) :
    ∀ᶠ n : ℕ in atTop,
      normalizedTranslationBoundaryThickness t n ≤ (1 / 2 : ℝ) := by
  exact (tendsto_normalizedTranslationBoundaryThickness_zero t).eventually
    (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

/-- Removing the prescribed boundary layer leaves points strictly inside both
the centered cube and its pullback by translation. -/
theorem cubeShrunkSet_translation_subset_openCube_inter_preimage
    {d : ℕ} (t : Vec d) (n : ℕ) :
    cubeShrunkSet (originCube d (n : ℤ))
        (normalizedTranslationBoundaryThickness t n) ⊆
      openCubeSet (originCube d (n : ℤ)) ∩
        (fun x => x + t) ⁻¹' openCubeSet (originCube d (n : ℤ)) := by
  intro x hx
  have hscale : 0 < cubeScaleFactor (originCube d (n : ℤ)) :=
    zpow_pos (by norm_num : (0 : ℝ) < 3) _
  have hthick : normalizedTranslationBoundaryThickness t n *
      cubeScaleFactor (originCube d (n : ℤ)) = ‖t‖ + 1 := by
    unfold normalizedTranslationBoundaryThickness
    field_simp [hscale.ne']
  constructor
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi : (-(1 / 2 : ℝ) + normalizedTranslationBoundaryThickness t n) *
          (3 : ℝ) ^ n ≤ x i ∧
        x i < ((1 / 2 : ℝ) - normalizedTranslationBoundaryThickness t n) *
          (3 : ℝ) ^ n := by
      simpa only [originCube, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add,
        cubeScaleFactor, zpow_natCast] using hx i
    have hnorm : 0 ≤ ‖t‖ := norm_nonneg t
    simp only [cubeScaleFactor_originCube, zpow_natCast] at hscale hthick
    obtain ⟨hlo, hup⟩ := hi
    rw [add_mul, hthick] at hlo
    rw [sub_mul, hthick] at hup
    simp only [zpow_natCast]
    exact ⟨by linarith only [hlo, hnorm], by linarith only [hup, hnorm]⟩
  · rw [mem_preimage, mem_openCubeSet_originCube_iff]
    intro i
    have hi : (-(1 / 2 : ℝ) + normalizedTranslationBoundaryThickness t n) *
          (3 : ℝ) ^ n ≤ x i ∧
        x i < ((1 / 2 : ℝ) - normalizedTranslationBoundaryThickness t n) *
          (3 : ℝ) ^ n := by
      simpa only [originCube, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add,
        cubeScaleFactor, zpow_natCast] using hx i
    have hti : |t i| ≤ ‖t‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm t i
    have htlo : -‖t‖ ≤ t i := (neg_le_of_abs_le hti)
    have hthi : t i ≤ ‖t‖ := le_trans (le_abs_self _) hti
    simp only [cubeScaleFactor_originCube, zpow_natCast] at hscale hthick
    obtain ⟨hlo, hup⟩ := hi
    rw [add_mul, hthick] at hlo
    rw [sub_mul, hthick] at hup
    simp only [Pi.add_apply, zpow_natCast]
    exact ⟨by linarith only [hlo, htlo], by linarith only [hup, hthi]⟩

/-- The part of the centered open cube lost under a fixed translation lies in
the explicit shrinking boundary layer. -/
theorem openCube_diff_translatePreimage_subset_boundaryLayer
    {d : ℕ} (t : Vec d) (n : ℕ) :
    openCubeSet (originCube d (n : ℤ)) \
        (fun x => x + t) ⁻¹' openCubeSet (originCube d (n : ℤ)) ⊆
      cubeBoundaryLayer (originCube d (n : ℤ))
        (normalizedTranslationBoundaryThickness t n) := by
  intro x hx
  refine ⟨openCubeSet_subset_cubeSet _ hx.1, ?_⟩
  intro hcore
  exact hx.2
    (cubeShrunkSet_translation_subset_openCube_inter_preimage t n hcore).2

/-- The relative volume of the explicit translation boundary layer tends to
zero. -/
theorem tendsto_relativeVolume_translationBoundaryLayer_zero
    {d : ℕ} (t : Vec d) :
    Tendsto
      (fun n : ℕ =>
        (volume (cubeBoundaryLayer (originCube d (n : ℤ))
          (normalizedTranslationBoundaryThickness t n))).toReal /
            cubeVolume (originCube d (n : ℤ)))
      atTop (nhds 0) := by
  let tau : ℕ → ℝ := normalizedTranslationBoundaryThickness t
  have htau : Tendsto tau atTop (nhds 0) :=
    tendsto_normalizedTranslationBoundaryThickness_zero t
  have hformula : ∀ᶠ n : ℕ in atTop,
      (volume (cubeBoundaryLayer (originCube d (n : ℤ)) (tau n))).toReal /
          cubeVolume (originCube d (n : ℤ)) =
        1 - (1 - 2 * tau n) ^ d := by
    filter_upwards
      [eventually_normalizedTranslationBoundaryThickness_le_half t]
      with n hn
    have htauNonneg : 0 ≤ tau n :=
      (normalizedTranslationBoundaryThickness_pos t n).le
    rw [volume_cubeBoundaryLayer_toReal_of_nonneg_le_half _ htauNonneg hn]
    have hvol : 0 < cubeVolume (originCube d (n : ℤ)) := cubeVolume_pos _
    rw [cubeVolume, mul_pow]
    field_simp [hvol.ne']
  have hright : Tendsto (fun n : ℕ => 1 - (1 - 2 * tau n) ^ d)
      atTop (nhds 0) := by
    have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have htwo : Tendsto (fun _n : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa only [mul_zero, sub_zero, one_pow, sub_self] using
      hone.sub ((hone.sub (htwo.mul htau)).pow d)
  exact hright.congr' (Filter.EventuallyEq.symm hformula)

end

end HighContrast
end Homogenization
