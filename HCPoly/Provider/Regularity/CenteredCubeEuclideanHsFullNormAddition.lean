/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CenteredCubeEuclideanHsAddition
import HCPoly.Provider.Regularity.CenteredCubeEuclideanHsFullNormConstantMatrix

/-!
# Addition on the physical centered-cube Euclidean Hs full norm

Pointwise addition obeys Minkowski's inequality on the normalized Euclidean
`L2` term.  Combining that estimate with the squared-energy triangle
bound gives a dimension-free addition estimate for the homogeneous physical
fractional full norm.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {m : ℤ}

private theorem euclideanNorm_add_le_fullNormAddition (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 (x + y)‖ ≤
    ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

/-- Minkowski's inequality for pointwise addition on the normalized physical
Euclidean `L2` term. -/
theorem centeredCubeNormalizedEuclideanLpENorm_add_le
    (F G : CenteredCubeEuclideanL2Field d m) :
    (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (centeredCubeEuclideanL2FieldAdd F G) ≤
      (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
        (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) G := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  calc
    eLpNorm (fun x ↦ euclideanNorm
        (centeredCubeEuclideanL2FieldAdd F G x)) 2
        (centeredCubeDomain d m).normalizedVolume ≤
      eLpNorm ((fun x ↦ euclideanNorm (F x)) +
        fun x ↦ euclideanNorm (G x)) 2
        (centeredCubeDomain d m).normalizedVolume := by
      apply eLpNorm_mono
      intro x
      simp only [centeredCubeEuclideanL2FieldAdd_apply, Pi.add_apply,
        Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
        abs_of_nonneg (add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))]
      exact euclideanNorm_add_le_fullNormAddition (F x) (G x)
    _ ≤ eLpNorm (fun x ↦ euclideanNorm (F x)) 2
          (centeredCubeDomain d m).normalizedVolume +
        eLpNorm (fun x ↦ euclideanNorm (G x)) 2
          (centeredCubeDomain d m).normalizedVolume :=
      eLpNorm_add_le F.euclideanMagnitudeMemL2.aestronglyMeasurable
        G.euclideanMagnitudeMemL2.aestronglyMeasurable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)

end

end HighContrast
end Homogenization
