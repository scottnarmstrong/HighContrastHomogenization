import HCPoly.Entry.Multiscale.ResponseInputs.HC2a_ReferenceCubePullback

/-!
# The Besov scale weight of the reference cube

The Besov scale weight `cubeBesovScaleWeight s Q = (cubeScaleFactor Q) ^ (-s)` assigns to a
triadic cube `Q` the geometric weight `3^{-s · scale Q}`, and the scale factor is
`cubeScaleFactor Q = 3 ^ (scale Q)`.  On the reference cube `originCube d t`, whose scale is `t`,
both collapse to elementary powers of `3`: the scale factor is `3 ^ t` and the weight is
`3^{-s t}`.  In particular the exponent `-1/2` weight is `3^{t/2}` and the exponent `0` weight is
`1`.  These are the weight evaluations used when the cutoff support of the response is expanded in
the cube Besov scale.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The scale factor of the reference cube `originCube d t` is `3 ^ t`, the integer power being
read as a real power: `cubeScaleFactor (originCube d t) = 3 ^ (t : ℝ)`. -/
theorem cubeScaleFactor_originCube {d : ℕ} (t : ℤ) :
    cubeScaleFactor (originCube d t) = (3 : ℝ) ^ (t : ℝ) :=
  (Homogenization.cubeScaleFactor_originCube t).trans (Real.rpow_intCast 3 t).symm

/-- The Besov scale weight of exponent `s` on the reference cube `originCube d t` equals
`3^{-s t}`: `cubeBesovScaleWeight s (originCube d t) = 3 ^ (-s * (t : ℝ))`. -/
theorem cubeBesovScaleWeight_originCube {d : ℕ} (s : ℝ) (t : ℤ) :
    cubeBesovScaleWeight s (originCube d t) = (3 : ℝ) ^ (-s * (t : ℝ)) := by
  unfold cubeBesovScaleWeight
  rw [cubeScaleFactor_originCube, mul_comm (-s) (t : ℝ),
    Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The exponent `-1/2` Besov scale weight of the reference cube `originCube d t` is the positive
power `3^{t/2}`: `cubeBesovScaleWeight (-(1/2)) (originCube d t) = 3 ^ ((t : ℝ) / 2)`. -/
theorem cubeBesovScaleWeight_neg_half_originCube {d : ℕ} (t : ℤ) :
    cubeBesovScaleWeight (-(1 / 2 : ℝ)) (originCube d t) = (3 : ℝ) ^ ((t : ℝ) / 2) := by
  rw [cubeBesovScaleWeight_originCube,
    show -(-(1 / 2 : ℝ)) * (t : ℝ) = (t : ℝ) / 2 by ring]

/-- The exponent `0` Besov scale weight of the reference cube `originCube d t` is `1`:
`cubeBesovScaleWeight 0 (originCube d t) = 1`. -/
theorem cubeBesovScaleWeight_zero_originCube {d : ℕ} (t : ℤ) :
    cubeBesovScaleWeight 0 (originCube d t) = 1 := by
  rw [cubeBesovScaleWeight_originCube,
    show -(0 : ℝ) * (t : ℝ) = 0 by ring, Real.rpow_zero]

end

end Homogenization.HighContrast.Multiscale
