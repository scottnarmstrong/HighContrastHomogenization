/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.TranslationBoundaryIntegralVanishing

/-!
# Vanishing normalized integrals on translation-lost cube regions

The exact portion of a centered cube lost after a fixed translation is
contained in the explicit shrinking boundary layer.  Hence its normalized
vector integral vanishes under the same scale-uniform `L²` certificate.
-/

namespace Homogenization
namespace HighContrast

open Filter MeasureTheory Set

noncomputable section

/-- The exact translation-lost region is measurable. -/
theorem measurableSet_openCube_diff_translatePreimage
    {d : ℕ} (t : Vec d) (n : ℕ) :
    MeasurableSet
      (openCubeSet (originCube d (n : ℤ)) \
        (fun x ↦ x + t) ⁻¹' openCubeSet (originCube d (n : ℤ))) :=
  (measurableSet_openCubeSet _).diff
    ((measurableSet_openCubeSet _).preimage
      (measurable_id.add measurable_const))

/-- A uniformly normalized-`L²` sequence has vanishing normalized vector
integral on the exact part of the centered cube lost under a fixed
translation. -/
theorem tendsto_norm_setIntegral_translationLostRegion_zero
    {d : ℕ} (t : Vec d) (F : ℕ → Vec d → Vec d)
    (hF : ∀ n : ℕ,
      MemLp (F n) (2 : ENNReal)
        (normalizedCubeMeasure (originCube d (n : ℤ))))
    (M : ℝ) (hM : ∀ n : ℕ,
      cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal) (F n) ≤ M) :
    Tendsto
      (fun n : ℕ ↦
        ‖∫ x in openCubeSet (originCube d (n : ℤ)) \
              (fun y ↦ y + t) ⁻¹' openCubeSet (originCube d (n : ℤ)),
            F n x ∂normalizedCubeMeasure (originCube d (n : ℤ))‖)
      atTop (nhds 0) := by
  let Q : ℕ → TriadicCube d := fun n ↦ originCube d (n : ℤ)
  let L : ℕ → Set (Vec d) := fun n ↦
    openCubeSet (Q n) \ (fun x ↦ x + t) ⁻¹' openCubeSet (Q n)
  let B : ℕ → Set (Vec d) := fun n ↦
    cubeBoundaryLayer (Q n) (normalizedTranslationBoundaryThickness t n)
  have hLB : ∀ n : ℕ, L n ⊆ B n := by
    intro n
    exact openCube_diff_translatePreimage_subset_boundaryLayer t n
  have hBMeasure : ∀ n : ℕ,
      (normalizedCubeMeasure (Q n)).real (B n) =
        (volume (B n)).toReal / cubeVolume (Q n) := by
    intro n
    exact normalizedCubeMeasure_real_eq_volume_toReal_div_cubeVolume
      (Q n) (measurableSet_cubeBoundaryLayer _ _)
      (cubeBoundaryLayer_subset_cubeSet _ _)
  have hMnonneg : 0 ≤ M :=
    (cubeLpNorm_nonneg (Q 0) (2 : ENNReal) (F 0)).trans (hM 0)
  have hupper : ∀ n : ℕ,
      ‖∫ x in L n, F n x ∂normalizedCubeMeasure (Q n)‖ ≤
        M * Real.sqrt
          ((volume (B n)).toReal / cubeVolume (Q n)) := by
    intro n
    have hmeasureMono :
        (normalizedCubeMeasure (Q n)).real (L n) ≤
          (normalizedCubeMeasure (Q n)).real (B n) :=
      measureReal_mono (hLB n)
    calc
      ‖∫ x in L n, F n x ∂normalizedCubeMeasure (Q n)‖ ≤
          cubeLpNorm (Q n) (2 : ENNReal) (F n) *
            Real.sqrt ((normalizedCubeMeasure (Q n)).real (L n)) :=
        norm_setIntegral_normalizedCubeMeasure_le_cubeLpNorm_mul_sqrt_measure
          (Q n) (measurableSet_openCube_diff_translatePreimage t n) (F n) (hF n)
      _ ≤ M * Real.sqrt ((normalizedCubeMeasure (Q n)).real (L n)) :=
        mul_le_mul_of_nonneg_right (hM n) (Real.sqrt_nonneg _)
      _ ≤ M * Real.sqrt ((normalizedCubeMeasure (Q n)).real (B n)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmeasureMono) hMnonneg
      _ = M * Real.sqrt ((volume (B n)).toReal / cubeVolume (Q n)) := by
        rw [hBMeasure n]
  have hratio : Tendsto
      (fun n : ℕ ↦ (volume (B n)).toReal / cubeVolume (Q n))
      atTop (nhds 0) := by
    simpa only [B, Q] using
      tendsto_relativeVolume_translationBoundaryLayer_zero t
  have hupperLimit : Tendsto
      (fun n : ℕ ↦ M * Real.sqrt
        ((volume (B n)).toReal / cubeVolume (Q n)))
      atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds.mul hratio.sqrt)
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n ↦ norm_nonneg _)
    (Filter.Eventually.of_forall hupper) hupperLimit

end

end HighContrast
end Homogenization
