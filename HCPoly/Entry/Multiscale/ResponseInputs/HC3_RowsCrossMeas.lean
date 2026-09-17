import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsStateFam
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCutoffPathInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCanRead

/-!
# Weighted cell averages of the crossed pairing are measurable in the sample

The oscillation half of the cutoff-mean row of `p.response.transfer` reads, on each cell `V` of a
triadic refinement of the terminal cell, the weighted cell average of the scalar crossed pairing
`⟨Y₂, ∇u⟩ + ⟨Y₁, a ∇u⟩` of the terminal optimizer against the deterministic dual variable `Y`.
Because `Y` is deterministic, that scalar is a fixed linear combination of the `2d` coordinates of
the doubled optimizer state, so its weighted cell average is the same linear combination of the
`2d` weighted coordinate averages, each of which is measurable in the sample by
`HC3_RowsStateFam`.  The coordinate averages are finite by `HC3_RowsCutoffPathInt`, which needs
only continuity of the weight.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The weighted cell average of the crossed pairing is the `Y`-combination of the `2d` weighted
coordinate averages, for an arbitrary doubled field whose coordinates are integrable on `V`. -/
private theorem volumeAverage_weighted_cross_eq_sum {d : ℕ} {V : Set (Vec d)}
    (eta : Vec d → ℝ) (X : Vec d → BlockVec d) (Y : BlockVec d)
    (h1 : ∀ i : Fin d, IntegrableOn (fun x => eta x * (X x).1 i) V)
    (h2 : ∀ i : Fin d, IntegrableOn (fun x => eta x * (X x).2 i) V) :
    volumeAverage V (fun x => eta x * (vecDot Y.2 (X x).1 + vecDot Y.1 (X x).2))
      = (∑ i : Fin d, Y.2 i * volumeAverage V (fun x => eta x * (X x).1 i))
        + ∑ i : Fin d, Y.1 i * volumeAverage V (fun x => eta x * (X x).2 i) := by
  classical
  have hs1 : ∀ i : Fin d, IntegrableOn (fun x => Y.2 i * (eta x * (X x).1 i)) V :=
    fun i => (h1 i).const_mul (Y.2 i)
  have hs2 : ∀ i : Fin d, IntegrableOn (fun x => Y.1 i * (eta x * (X x).2 i)) V :=
    fun i => (h2 i).const_mul (Y.1 i)
  have hsum1 : IntegrableOn (fun x => ∑ i : Fin d, Y.2 i * (eta x * (X x).1 i)) V :=
    integrable_finsetSum _ fun i _ => hs1 i
  have hsum2 : IntegrableOn (fun x => ∑ i : Fin d, Y.1 i * (eta x * (X x).2 i)) V :=
    integrable_finsetSum _ fun i _ => hs2 i
  have hsplit : (fun x => eta x * (vecDot Y.2 (X x).1 + vecDot Y.1 (X x).2))
      = (fun x => ∑ i : Fin d, Y.2 i * (eta x * (X x).1 i))
        + fun x => ∑ i : Fin d, Y.1 i * (eta x * (X x).2 i) := by
    funext x
    simp only [Pi.add_apply, vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, volumeAverage_add hsum1 hsum2,
    volumeAverage_sum Finset.univ (fun i x => Y.2 i * (eta x * (X x).1 i))
      (fun i _ => hs1 i),
    volumeAverage_sum Finset.univ (fun i x => Y.1 i * (eta x * (X x).2 i))
      (fun i _ => hs2 i)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (fun x => Y.2 i * (eta x * (X x).1 i))
        = Y.2 i • fun x => eta x * (X x).1 i by funext x; simp [smul_eq_mul]]
    exact volumeAverage_smul V (Y.2 i) _
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (fun x => Y.1 i * (eta x * (X x).2 i))
        = Y.1 i • fun x => eta x * (X x).2 i by funext x; simp [smul_eq_mul]]
    exact volumeAverage_smul V (Y.1 i) _

/-- **The weighted cell average of the crossed pairing is measurable in the sample, minus sign.**
For a continuous weight whose indicator is square-integrable on the terminal cell and any
measurable subcell `V`, the `V`-average of `eta · (⟨Y₂, ∇u⟩ + ⟨Y₁, a_- ∇u⟩)` is a measurable
function of the coefficient sample, for an arbitrary family of terminal maximizers. -/
theorem measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta)
    (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) := by
  classical
  have hI := fun (a : CoeffSpace d) (i : Fin d) =>
    integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm t uM hV hVU
      hetac a i
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)))
      = fun a : CoeffSpace d =>
        (∑ i : Fin d, Y.2 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) (Sum.inl i)))
          + ∑ i : Fin d, Y.1 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffMinus F a) (uM a) x) (Sum.inr i)) := by
    funext a
    exact volumeAverage_weighted_cross_eq_sum eta
      (optimizerField (respCoeffMinus F a) (uM a)) Y (fun i => (hI a i).1) (fun i => (hI a i).2)
  rw [hEq]
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_)
    (Finset.measurable_sum _ fun i _ => ?_)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffMinus P jStar hjStar F hm t e
      (Sum.inl i) uM hmax hV hVU heta).const_mul (Y.2 i)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffMinus P jStar hjStar F hm t e
      (Sum.inr i) uM hmax hV hVU heta).const_mul (Y.1 i)

/-- **The weighted cell average of the crossed pairing is measurable in the sample, plus sign.**
The adjoint twin of
`measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus`. -/
theorem measurable_volumeAverage_weighted_cross_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta)
    (heta : MemScalarL2 (respCell jStar F t) (V.indicator eta)) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) := by
  classical
  have hI := fun (a : CoeffSpace d) (i : Fin d) =>
    integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm t uP hV hVU
      hetac a i
  have hEq : (fun a : CoeffSpace d => volumeAverage V (fun x => eta x *
        (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)))
      = fun a : CoeffSpace d =>
        (∑ i : Fin d, Y.2 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) (Sum.inl i)))
          + ∑ i : Fin d, Y.1 i * volumeAverage V (fun x => eta x *
            toFullBlockVec (optimizerField (respCoeffPlus F a) (uP a) x) (Sum.inr i)) := by
    funext a
    exact volumeAverage_weighted_cross_eq_sum eta
      (optimizerField (respCoeffPlus F a) (uP a)) Y (fun i => (hI a i).1) (fun i => (hI a i).2)
  rw [hEq]
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_)
    (Finset.measurable_sum _ fun i _ => ?_)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffPlus P jStar hjStar F hm t e
      (Sum.inl i) uP hmax hV hVU heta).const_mul (Y.2 i)
  · exact (measurable_volumeAverage_weighted_optimizerField_respCoeffPlus P jStar hjStar F hm t e
      (Sum.inr i) uP hmax hV hVU heta).const_mul (Y.1 i)

/-- **The unweighted cell average of the crossed pairing is measurable in the sample, minus
sign.**  The constant-weight case of
`measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus`; the indicator of a
measurable subcell by the constant `1` is square-integrable on the terminal cell. -/
theorem measurable_volumeAverage_cross_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x =>
        vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  simpa only [one_mul] using
    measurable_volumeAverage_weighted_cross_optimizerField_respCoeffMinus P jStar hjStar F hm t e
      uM hmax hV hVU (eta := fun _ : Vec d => (1 : ℝ)) continuous_const
      (memScalarL2_indicator_one
        (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t) hV) Y

/-- **The unweighted cell average of the crossed pairing is measurable in the sample, plus
sign.**  The adjoint twin of
`measurable_volumeAverage_cross_optimizerField_respCoeffMinus`. -/
theorem measurable_volumeAverage_cross_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t) (Y : BlockVec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x =>
        vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  simpa only [one_mul] using
    measurable_volumeAverage_weighted_cross_optimizerField_respCoeffPlus P jStar hjStar F hm t e
      uP hmax hV hVU (eta := fun _ : Vec d => (1 : ℝ)) continuous_const
      (memScalarL2_indicator_one
        (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t) hV) Y

end

end Homogenization.HighContrast.Multiscale
