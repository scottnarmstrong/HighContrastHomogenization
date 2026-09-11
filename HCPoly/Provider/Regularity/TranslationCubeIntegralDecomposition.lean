/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.TranslationLostRegionIntegralVanishing
import Homogenization.Geometry.Translation

/-!
# Exact decomposition of translated normalized cube integrals

After changing variables on the common part of a cube and its translate, the
difference of the two normalized cube integrals is exactly the difference of
two lost-region integrals, for the translations `t` and `-t`.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory Set

noncomputable section

/-- A normalized cube integral is the inverse cube volume times the ordinary
set integral over the open cube. -/
theorem integral_normalizedCubeMeasure_eq_inv_smul_setIntegral_openCube
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d) :
    ∫ x, F x ∂normalizedCubeMeasure Q =
      (cubeVolume Q)⁻¹ • ∫ x in openCubeSet Q, F x ∂volume := by
  rw [normalizedCubeMeasure, integral_smul_measure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg Q))]

/-- The same normalization identity for a measurable subset of the cube. -/
theorem setIntegral_normalizedCubeMeasure_eq_inv_smul_setIntegral_volume
    {d : ℕ} (Q : TriadicCube d) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSQ : S ⊆ cubeSet Q) (F : Vec d → Vec d) :
    ∫ x in S, F x ∂normalizedCubeMeasure Q =
      (cubeVolume Q)⁻¹ • ∫ x in S, F x ∂volume := by
  rw [normalizedCubeMeasure, Measure.restrict_smul, integral_smul_measure,
    cubeMeasure, Measure.restrict_restrict hS, inter_eq_left.mpr hSQ]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg Q))]

/-- Exact lost-region decomposition for translation of a normalized cube
integral. -/
theorem integral_translate_sub_integral_normalizedCubeMeasure_eq_lostRegions
    {d : ℕ} (Q : TriadicCube d) (t : Vec d) (F : Vec d → Vec d)
    (hF : IntegrableOn F (openCubeSet Q) volume)
    (hFt : IntegrableOn (fun x ↦ F (x + t)) (openCubeSet Q) volume) :
    (∫ x, F (x + t) ∂normalizedCubeMeasure Q) -
        ∫ x, F x ∂normalizedCubeMeasure Q =
      (∫ x in openCubeSet Q \
          (fun y ↦ y + t) ⁻¹' openCubeSet Q,
          F (x + t) ∂normalizedCubeMeasure Q) -
        ∫ x in openCubeSet Q \
          (fun y ↦ y + (-t)) ⁻¹' openCubeSet Q,
          F x ∂normalizedCubeMeasure Q := by
  let A : Set (Vec d) := openCubeSet Q
  let P : Set (Vec d) := (fun x ↦ x + t) ⁻¹' A
  let N : Set (Vec d) := (fun x ↦ x + (-t)) ⁻¹' A
  have hA : MeasurableSet A := measurableSet_openCubeSet Q
  have hP : MeasurableSet P :=
    hA.preimage (measurable_id.add measurable_const)
  have hN : MeasurableSet N :=
    hA.preimage (measurable_id.add measurable_const)
  have htranslate : translateSet t (A ∩ P) = A ∩ N := by
    ext y
    simp only [mem_translateSet_iff_sub_mem, mem_inter_iff, mem_preimage, A, P, N]
    constructor
    · rintro ⟨hyA, hytA⟩
      constructor
      · simpa [sub_eq_add_neg, add_assoc] using hytA
      · simpa [sub_eq_add_neg] using hyA
    · rintro ⟨hyA, hynA⟩
      constructor
      · simpa [sub_eq_add_neg] using hynA
      · simpa [sub_eq_add_neg, add_assoc] using hyA
  have hcommon :
      ∫ x in A ∩ P, F (x + t) ∂volume =
        ∫ x in A ∩ N, F x ∂volume := by
    rw [setIntegral_comp_addRight_translateSet t (A ∩ P) F, htranslate]
  have hsplitT :
      ∫ x in A, F (x + t) ∂volume =
        (∫ x in A ∩ P, F (x + t) ∂volume) +
          ∫ x in A \ P, F (x + t) ∂volume := by
    exact (integral_inter_add_diff hP hFt).symm
  have hsplitF :
      ∫ x in A, F x ∂volume =
        (∫ x in A ∩ N, F x ∂volume) +
          ∫ x in A \ N, F x ∂volume := by
    exact (integral_inter_add_diff hN hF).symm
  have hvolume :
      (∫ x in A, F (x + t) ∂volume) - ∫ x in A, F x ∂volume =
        (∫ x in A \ P, F (x + t) ∂volume) -
          ∫ x in A \ N, F x ∂volume := by
    rw [hsplitT, hsplitF, hcommon]
    abel
  have hAPSub : A \ P ⊆ cubeSet Q :=
    fun x hx ↦ openCubeSet_subset_cubeSet Q hx.1
  have hANSub : A \ N ⊆ cubeSet Q :=
    fun x hx ↦ openCubeSet_subset_cubeSet Q hx.1
  rw [integral_normalizedCubeMeasure_eq_inv_smul_setIntegral_openCube,
    integral_normalizedCubeMeasure_eq_inv_smul_setIntegral_openCube,
    setIntegral_normalizedCubeMeasure_eq_inv_smul_setIntegral_volume
      Q (hA.diff hP) hAPSub,
    setIntegral_normalizedCubeMeasure_eq_inv_smul_setIntegral_volume
      Q (hA.diff hN) hANSub]
  change (cubeVolume Q)⁻¹ • (∫ x in A, F (x + t) ∂volume) -
      (cubeVolume Q)⁻¹ • (∫ x in A, F x ∂volume) =
    (cubeVolume Q)⁻¹ • (∫ x in A \ P, F (x + t) ∂volume) -
      (cubeVolume Q)⁻¹ • (∫ x in A \ N, F x ∂volume)
  simpa only [smul_sub] using congrArg ((cubeVolume Q)⁻¹ • ·) hvolume

end

end HighContrast
end Homogenization
