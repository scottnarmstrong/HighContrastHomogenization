import HCPoly.Entry.Geometry.RoundedGridComparison

/-!
# Geometric consequences for the projective step

The two lemmas here assemble the already-proved projective metric triangle
inequality and exact geometry-update displacement.  They correspond to the
eccentricity conclusion of `l.projective.step`
(near `l.projective.step`).
-/

namespace Homogenization.HighContrast.Geometry

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Half-log eccentricity is 1-Lipschitz for the projective distance from the
identity. -/
theorem log_eccentricity_le_add_projectiveDistance
    {d : ℕ} [NeZero d] {m m' : Mat d} (hm : m.PosDef) (hm' : m'.PosDef) :
    1 / 2 * Real.log (‖m'‖ * ‖m'⁻¹‖) ≤
      1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) + projectiveDistance m m' := by
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have htri := projectiveDistance_triangle hone hm hm'
  rwa [projectiveDistance_one_eq_log_eccentricity hm,
    projectiveDistance_one_eq_log_eccentricity hm'] at htri

/-- The geometry update increases half-log eccentricity by at most the
requested step, for every positive `ε`. -/
theorem log_eccentricity_geometryUpdate_le
    {d : ℕ} [NeZero d] {m mStar : Mat d} (hm : m.PosDef) (hStar : mStar.PosDef)
    {ε : ℝ} (hε : 0 < ε) :
    1 / 2 * Real.log (‖geometryUpdate ε m mStar‖ * ‖(geometryUpdate ε m mStar)⁻¹‖) ≤
      1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) + ε := by
  have hupd : (geometryUpdate ε m mStar).PosDef := geometryUpdate_posDef hm hStar ε
  have hecc := log_eccentricity_le_add_projectiveDistance hm hupd
  have hstep := projectiveDistance_geometryUpdate_le hm hStar hε
  linarith

end

end Homogenization.HighContrast.Geometry
