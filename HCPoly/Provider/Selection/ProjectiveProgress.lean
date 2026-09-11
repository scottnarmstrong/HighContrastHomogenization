/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.NearIsometry
import HCPoly.Provider.ShortHop.Normalization

/-!
# Projective progress across one bridge

The distance from the new witness to the new canonical metric is estimated by
inserting the old terminal metric and the old checkpoint metric.  Determinant
loss controls the latter insertion, while the near-isometry comparison controls
the former.  These are the two alternatives in the decrease of the distance to
the canonical metric at a change of geometry, in the proof of
`p.global.selection`.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- The projective error
`ε_pr(η) = (1/2) log ((1+η)/(1-η))` of
`e.global.selection.metric.comparison`. -/
def projectiveError (η : ℝ) : ℝ :=
  (1 / 2) * Real.log ((1 + η) / (1 - η))

/-- The defining equation for the projective error. -/
theorem projectiveError_eq (η : ℝ) :
    projectiveError η = (1 / 2) * Real.log ((1 + η) / (1 - η)) := rfl

private theorem projective_determinant_loss
    (hd : 2 ≤ d) {A F : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hF : (toFullBlockMat F).PosDef)
    (hFA : toFullBlockMat F ≤ toFullBlockMat A) :
    projDist (canonicalMetric A) (canonicalMetric F) ≤
      ((d : ℝ) / 2) * (Real.log (detRoot d A) - Real.log (detRoot d F)) := by
  have hdpos : 0 < d := lt_of_lt_of_le two_pos hd
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  have hbound := projDist_canonMetric_le_log_det_div hdpos hA hF hFA
  have hlogA : Real.log (detRoot d A) =
      (d : ℝ)⁻¹ * Real.log (toFullBlockMat A).det := by
    rw [detRoot, Real.log_rpow hA.det_pos, mul_comm]
  have hlogF : Real.log (detRoot d F) =
      (d : ℝ)⁻¹ * Real.log (toFullBlockMat F).det := by
    rw [detRoot, Real.log_rpow hF.det_pos, mul_comm]
  have hrw : ((d : ℝ) / 2) *
        (Real.log (detRoot d A) - Real.log (detRoot d F)) =
      (1 / 2) * Real.log ((toFullBlockMat A).det / (toFullBlockMat F).det) := by
    rw [hlogA, hlogF, Real.log_div hA.det_pos.ne' hF.det_pos.ne']
    field_simp
  rw [hrw]
  exact hbound

/-- **A nonfinal bridge makes one hop of projective progress.**  This is the
projective progress at a partial geometry change, in the general block form used
by the selection engine. -/
theorem projective_progress_nonfinal
    (hd : 2 ≤ d) {A F A' : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hF : (toFullBlockMat F).PosDef)
    (hA' : (toFullBlockMat A').PosDef)
    (hFA : toFullBlockMat F ≤ toFullBlockMat A)
    {deltaStage etaX chop : ℝ}
    (hdeltaStage : deltaStage =
      Real.log (detRoot d A) - Real.log (detRoot d F))
    (hetaX0 : 0 ≤ etaX) (hetaX1 : etaX ≤ 1 / 4)
    (hlow : (1 - etaX) • toFullBlockMat F ≤ toFullBlockMat A')
    (hhigh : toFullBlockMat A' ≤ (1 + etaX) • toFullBlockMat F)
    {mu mu' : Mat d} (hmu : mu.PosDef) (hmu' : mu'.PosDef)
    (hpath : projDist mu' (canonicalMetric F) =
      projDist mu (canonicalMetric F) - chop) :
    projDist mu' (canonicalMetric A') ≤
      projDist mu (canonicalMetric A) - chop +
        ((d : ℝ) / 2) * deltaStage + projectiveError etaX := by
  haveI : Nonempty (Fin d) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩⟩
  have hcanonA : (canonicalMetric A).PosDef := posDef_canonMetric hA
  have hcanonF : (canonicalMetric F).PosDef := posDef_canonMetric hF
  have hcanonA' : (canonicalMetric A').PosDef := posDef_canonMetric hA'
  have hdet := projective_determinant_loss hd hA hF hFA
  have hnear : projDist (canonicalMetric F) (canonicalMetric A') ≤
      (1 / 2) * Real.log ((1 + etaX) / (1 - etaX)) := by
    simpa [canonicalMetric] using (canonNearIsometry hd hF hA' hetaX0 (by
      linarith only [hetaX1]) hlow hhigh).2
  have hfirst := projDist_triangle hmu' hcanonF hcanonA'
  have hsecond := projDist_triangle hmu hcanonA hcanonF
  rw [hdeltaStage]
  exact le_trans hfirst (by
    rw [projectiveError_eq]
    linarith only [hpath, hsecond, hdet, hnear])

/-- **A final bridge ends within the near-isometry error.**  This is the
projective distance after a hop that reaches the canonical candidate. -/
theorem projective_progress_final
    (hd : 2 ≤ d) {F A' : BlockMat d}
    (hF : (toFullBlockMat F).PosDef) (hA' : (toFullBlockMat A').PosDef)
    {etaX : ℝ} (hetaX0 : 0 ≤ etaX) (hetaX1 : etaX ≤ 1 / 4)
    (hlow : (1 - etaX) • toFullBlockMat F ≤ toFullBlockMat A')
    (hhigh : toFullBlockMat A' ≤ (1 + etaX) • toFullBlockMat F) :
    projDist (canonicalMetric F) (canonicalMetric A') ≤ projectiveError etaX := by
  rw [projectiveError_eq]
  exact (canonNearIsometry hd hF hA' hetaX0 (by
    linarith only [hetaX1]) hlow hhigh).2

end

end Selection
end HighContrast
end Homogenization
