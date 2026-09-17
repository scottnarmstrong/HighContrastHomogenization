import HCPoly.Entry.Multiscale.ResponseInputs.OptimizerReadoutGlue

/-!
# Cell averages of the canonical optimizer depend measurably on the sample

The weak quantity `W^\pm` of the response estimate `e.response.weak.estimate` is a volume
average, over a measurable subcell, of a coordinate of the canonical optimizer state of a
recentred coefficient sample.  This file records the specialization of the localized weighted
readout to the constant weight `1`, so that a plain cell average is measurable in the sample;
the indicator of a measurable set by a constant is bounded and therefore locally `L²`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The indicator of a measurable set by the constant `1` is square-integrable on every open
bounded convex domain: it is measurable, bounded by `1`, and the restricted Lebesgue measure is
finite.  This is the constant-weight input to the cell averages of the weak quantity
`e.response.weak.estimate`. -/
theorem memScalarL2_indicator_one {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hV : MeasurableSet V) :
    MemScalarL2 U (V.indicator (fun _ : Vec d => (1 : ℝ))) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  refine MemLp.of_bound ?_ 1 (Filter.Eventually.of_forall ?_)
  · exact (measurable_const.indicator hV).aestronglyMeasurable
  · intro x
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx, norm_one, le_refl]
    · simp only [Set.indicator_of_notMem hx, norm_zero, zero_le_one]

/-- The cell average of a coordinate of the canonical minus optimizer state is measurable in the
coefficient sample, for every measurable subcell of the adapted cell.  This is the
constant-weight case of the localized weighted readout entering the weak quantity `W^-` of
`e.response.weak.estimate`. -/
theorem measurable_cellAverage_canonicalRespCoeffMinus {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) (alpha : BlockCoord d)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x) alpha) := by
  simpa only [one_mul] using
    (measurable_volumeAverage_weighted_canonicalRespCoeffMinus q hq t F p r alpha hV hVU
      (eta := fun _ : Vec d => (1 : ℝ))
      (memScalarL2_indicator_one (adaptedCell_isOpenBoundedConvexDomain q hq t) hV))

/-- The cell average of a coordinate of the canonical plus optimizer state is measurable in the
coefficient sample, for every measurable subcell of the adapted cell.  This is the
constant-weight case of the localized weighted readout entering the weak quantity `W^+` of
`e.response.weak.estimate`. -/
theorem measurable_cellAverage_canonicalRespCoeffPlus {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) (alpha : BlockCoord d)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x) alpha) := by
  simpa only [one_mul] using
    (measurable_volumeAverage_weighted_canonicalRespCoeffPlus q hq t F p r alpha hV hVU
      (eta := fun _ : Vec d => (1 : ℝ))
      (memScalarL2_indicator_one (adaptedCell_isOpenBoundedConvexDomain q hq t) hV))

end

end Homogenization.HighContrast.Multiscale
