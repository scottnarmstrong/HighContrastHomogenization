/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorDecay.ContinuousKH1Interpolation
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
import Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge

/-!
# Fractional interpolation for centered-cube H1 vector fields

The scale-normalized coordinate gradient sum is invariant under pullback to
the centered unit cube.  Combining this transport with continuous
interpolation gives a quantitative Hs bound without a boundary condition.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- The represented field of a coordinatewise centered-cube H1 function,
with its Euclidean L2 certificate. -/
noncomputable def CubeVectorH1Function.centeredEuclideanL2Field
    {d : ℕ} {m : ℤ} (G : CubeVectorH1Function (originCube d m)) :
    CenteredCubeEuclideanL2Field d m where
  toField := G.toField
  euclideanMemL2 := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    rw [memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply,
      CubeVectorH1Function.toField] using
      (G.coord i).memL2_normalizedCubeMeasure

end

end Homogenization
