/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.TranslationCubeIntegralDecomposition

/-!
# Stability of normalized cube integrals under fixed translation

The exact lost-region decomposition and the two vanishing boundary errors
imply that normalized centered-cube integrals are asymptotically unchanged by
any fixed translation.
-/

namespace Homogenization
namespace HighContrast

open Filter MeasureTheory Set

noncomputable section

private theorem integrableOn_openCube_of_memLp_normalizedCubeMeasure
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp F (2 : ENNReal) (normalizedCubeMeasure Q)) :
    IntegrableOn F (openCubeSet Q) volume := by
  have hInt : Integrable F (normalizedCubeMeasure Q) :=
    hF.integrable (by norm_num)
  rw [normalizedCubeMeasure, cubeMeasure] at hInt
  have hscale : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have hCube : Integrable F (volume.restrict (cubeSet Q)) :=
    (integrable_smul_measure hscale ENNReal.ofReal_ne_top).mp hInt
  exact hCube.mono_measure
    (Measure.restrict_mono_set volume (openCubeSet_subset_cubeSet Q))

/-- If a field and its fixed translate have one scale-uniform normalized
`L²` bound on the centered exhaustion, then the norm of the difference of
their normalized cube integrals tends to zero. -/
theorem tendsto_norm_integral_translate_sub_integral_normalizedCubeMeasure_zero
    {d : ℕ} (t : Vec d) (F : Vec d → Vec d)
    (hF : ∀ n : ℕ,
      MemLp F (2 : ENNReal)
        (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hFt : ∀ n : ℕ,
      MemLp (fun x ↦ F (x + t)) (2 : ENNReal)
        (normalizedCubeMeasure (originCube d (n : ℤ))))
    (M : ℝ)
    (hM : ∀ n : ℕ,
      cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal) F ≤ M)
    (hMt : ∀ n : ℕ,
      cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal)
        (fun x ↦ F (x + t)) ≤ M) :
    Tendsto
      (fun n : ℕ ↦
        ‖(∫ x, F (x + t) ∂normalizedCubeMeasure (originCube d (n : ℤ))) -
          ∫ x, F x ∂normalizedCubeMeasure (originCube d (n : ℤ))‖)
      atTop (nhds 0) := by
  let Q : ℕ → TriadicCube d := fun n ↦ originCube d (n : ℤ)
  let Eplus : ℕ → Vec d := fun n ↦
    ∫ x in openCubeSet (Q n) \
        (fun y ↦ y + t) ⁻¹' openCubeSet (Q n),
      F (x + t) ∂normalizedCubeMeasure (Q n)
  let Eminus : ℕ → Vec d := fun n ↦
    ∫ x in openCubeSet (Q n) \
        (fun y ↦ y + (-t)) ⁻¹' openCubeSet (Q n),
      F x ∂normalizedCubeMeasure (Q n)
  have hplus : Tendsto (fun n ↦ ‖Eplus n‖) atTop (nhds 0) := by
    simpa only [Eplus, Q] using
      tendsto_norm_setIntegral_translationLostRegion_zero
        t (fun _n x ↦ F (x + t)) hFt M hMt
  have hminus : Tendsto (fun n ↦ ‖Eminus n‖) atTop (nhds 0) := by
    simpa only [Eminus, Q] using
      tendsto_norm_setIntegral_translationLostRegion_zero
        (-t) (fun _n ↦ F) hF M hM
  have herrors : Tendsto (fun n ↦ ‖Eplus n - Eminus n‖)
      atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n ↦ norm_nonneg _)
      (Filter.Eventually.of_forall fun n ↦ norm_sub_le _ _)
    simpa only [add_zero] using hplus.add hminus
  have hdecomp : ∀ n : ℕ,
      (∫ x, F (x + t) ∂normalizedCubeMeasure (Q n)) -
          ∫ x, F x ∂normalizedCubeMeasure (Q n) =
        Eplus n - Eminus n := by
    intro n
    exact integral_translate_sub_integral_normalizedCubeMeasure_eq_lostRegions
      (Q n) t F
      (integrableOn_openCube_of_memLp_normalizedCubeMeasure (Q n) F (hF n))
      (integrableOn_openCube_of_memLp_normalizedCubeMeasure
        (Q n) (fun x ↦ F (x + t)) (hFt n))
  exact herrors.congr'
    (Filter.Eventually.of_forall fun n ↦ congrArg norm (hdecomp n).symm)

end

end HighContrast
end Homogenization
