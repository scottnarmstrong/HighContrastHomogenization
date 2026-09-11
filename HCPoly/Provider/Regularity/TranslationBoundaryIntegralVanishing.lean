/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.BoundarySetIntegralL2
import HCPoly.Provider.Regularity.TranslationBoundaryGeometry

/-!
# Vanishing normalized integrals on translation boundary layers

The geometric translation boundary has vanishing relative volume.  Combined
with a scale-uniform normalized `L²` bound, the normalized vector integral over
that boundary therefore tends to zero.
-/

namespace Homogenization
namespace HighContrast

open Filter MeasureTheory Set

noncomputable section

/-- On a measurable subset of a cube, normalized cube measure is ordinary
volume divided by cube volume. -/
theorem normalizedCubeMeasure_real_eq_volume_toReal_div_cubeVolume
    {d : ℕ} (Q : TriadicCube d) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSQ : S ⊆ cubeSet Q) :
    (normalizedCubeMeasure Q).real S =
      (volume S).toReal / cubeVolume Q := by
  rw [normalizedCubeMeasure, measureReal_ennreal_smul_apply, cubeMeasure,
    measureReal_restrict_apply hS, inter_eq_left.mpr hSQ]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg Q))]
  rw [Measure.real_def, div_eq_inv_mul]

end

end HighContrast
end Homogenization
