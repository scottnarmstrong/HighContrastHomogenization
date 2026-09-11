/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.TranslationCubeIntegralStability
import HCPoly.Provider.Regularity.CorrectorGlobalRepresentative
import HCPoly.Provider.Regularity.LocalGradientTranslation

/-!
# Translation stability for global corrector-gradient representatives

The glued global gradient of every normalized local carrier belongs to
normalized `L²` on each exhaustion cube, as does every fixed translate.  Thus
the general translated-cube integral theorem specializes with only the two
uniform quantitative bounds left to supply.
-/

namespace Homogenization
namespace HighContrast

open Filter MeasureTheory

noncomputable section

/-- The glued global gradient representative belongs to normalized `L²` on
every centered exhaustion cube. -/
theorem NormalizedLocalH1Carrier.memLp_globalGradientRepresentative_normalizedCubeMeasure
    {d : ℕ} (Phi : NormalizedLocalH1Carrier d) (n : ℕ) :
    MemLp Phi.globalGradientRepresentative (2 : ENNReal)
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  have hLocal := Phi.memLp_globalGradientRepresentative n
  have hScaled := hLocal.smul_measure
    (ENNReal.ofReal_ne_top :
      ENNReal.ofReal ((cubeVolume (originCube d (n : ℤ)))⁻¹) ≠ ⊤)
  simpa only [volumeMeasureOn, localGradientCube, normalizedCubeMeasure,
    cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hScaled

/-- Every fixed translate of the glued global gradient representative also
belongs to normalized `L²` on every centered exhaustion cube. -/
theorem NormalizedLocalH1Carrier.memLp_globalGradientRepresentative_translate_normalizedCubeMeasure
    {d : ℕ} (Phi : NormalizedLocalH1Carrier d) (t : Vec d) (n : ℕ) :
    MemLp (fun x ↦ Phi.globalGradientRepresentative (x + t)) (2 : ENNReal)
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  have hTranslated : MemVectorL2 (localGradientCube d n)
      (fun x ↦ Phi.globalGradientRepresentative (x + t)) :=
    memVectorL2_translate_localGradientCube t Phi.globalGradientRepresentative
      (fun q ↦ Phi.memLp_globalGradientRepresentative q) n
  have hScaled := hTranslated.smul_measure
    (ENNReal.ofReal_ne_top :
      ENNReal.ofReal ((cubeVolume (originCube d (n : ℤ)))⁻¹) ≠ ⊤)
  simpa only [volumeMeasureOn, localGradientCube, normalizedCubeMeasure,
    cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hScaled

/-- Under uniform normalized `L²` bounds for a glued corrector gradient and
its fixed translate, their centered normalized cube integrals have vanishing
difference. -/
theorem NormalizedLocalH1Carrier.tendsto_norm_integral_globalGradient_translate_sub_zero
    {d : ℕ} (Phi : NormalizedLocalH1Carrier d) (t : Vec d) (M : ℝ)
    (hM : ∀ n : ℕ,
      cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal)
        Phi.globalGradientRepresentative ≤ M)
    (hMt : ∀ n : ℕ,
      cubeLpNorm (originCube d (n : ℤ)) (2 : ENNReal)
        (fun x ↦ Phi.globalGradientRepresentative (x + t)) ≤ M) :
    Tendsto
      (fun n : ℕ ↦
        ‖(∫ x, Phi.globalGradientRepresentative (x + t)
            ∂normalizedCubeMeasure (originCube d (n : ℤ))) -
          ∫ x, Phi.globalGradientRepresentative x
            ∂normalizedCubeMeasure (originCube d (n : ℤ))‖)
      atTop (nhds 0) := by
  exact tendsto_norm_integral_translate_sub_integral_normalizedCubeMeasure_zero
    t Phi.globalGradientRepresentative
      (fun n ↦ Phi.memLp_globalGradientRepresentative_normalizedCubeMeasure n)
      (fun n ↦
        Phi.memLp_globalGradientRepresentative_translate_normalizedCubeMeasure t n)
      M hM hMt

end

end HighContrast
end Homogenization
