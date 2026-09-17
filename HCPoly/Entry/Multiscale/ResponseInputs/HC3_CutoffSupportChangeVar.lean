import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65a

/-!
# The change of variables from an adapted cell to the reference cube

The adapted cell `HighContrast.adaptedCell q t` of generation `t` is the image of the reference open
cube `openCubeSet (originCube d t)` under the linear map `y ↦ q y`
(`image_openCubeSet_originCube_eq_adaptedCell`).  This file records the two elementary facts that
let the normalized averages on the two sides be identified: the aligned cell at lattice index `0`
is the centred adapted cell, and translating the reference cube by the zero lattice index fixes it.
Together with `cubeAverage_comp_matVecMul`, these transport a normalized average on the adapted
cell to the reference cube, which is the change of variables behind the adapted-to-Euclidean
comparison, HC Lemma 2.15, (2.127)--(2.128).
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Translating the reference cube `originCube d t` by the zero lattice index leaves the cube
unchanged. -/
theorem translateCube_zero {d : ℕ} (t : ℤ) :
    translateCube (0 : Fin d → ℤ) (originCube d t) = originCube d t := by
  unfold translateCube
  have h : (fun i => (originCube d t).index i + (0 : Fin d → ℤ) i) = (originCube d t).index := by
    funext i; simp
  rw [h]

/-- The normalized average of `f` over the adapted cell `HighContrast.adaptedCell q t` equals the
normalized average of the pulled-back function `y ↦ f (matVecMul q y)` over the reference cube
`originCube d t`.  This is the change of variables `x = q y` for normalized averages, behind the
adapted-to-Euclidean comparison of HC Lemma 2.15, (2.127)--(2.128). -/
theorem volumeAverage_adaptedCell_eq_cubeAverage_comp {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (f : Vec d → ℝ) :
    volumeAverage (HighContrast.adaptedCell q t) f
      = cubeAverage (originCube d t) (fun y => f (matVecMul q y)) := by
  have hcov := cubeAverage_comp_matVecMul hq t (0 : Fin d → ℤ) f
  rw [b130_adaptedCellAtCenter_zero q t, translateCube_zero (d := d) t] at hcov
  exact hcov.symm

end

end Homogenization.HighContrast.Multiscale
