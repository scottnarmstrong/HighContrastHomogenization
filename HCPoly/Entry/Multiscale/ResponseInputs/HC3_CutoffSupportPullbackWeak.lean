import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportState
import HCPoly.Entry.Multiscale.ResponseInputs.HC2a_ReferenceCubePullback

/-!
# The pulled-back cube seminorms of a square-integrable doubled field

The slotwise pullback bounds of the cutoff argument, `partialSeminorm_pullback_fst_le` and
`partialSeminorm_pullback_snd_le`, take as side conditions the integrability of the squared
Euclidean length of the metric-scaled doubled field together with its a.e. strong measurability.
This file supplies both from the single hypothesis that all `2d` coordinates of the field are
square integrable on the adapted cell.

Paper: the cutoff estimate `e.response.cutoff.estimate` and its pullback to the reference cube.
-/

open Homogenization.HighContrast (matSqrt)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The metric scaling of a doubled field, by `m^{1/2}` in the first slot and `m^{-1/2}` in the
second, carries square integrable coordinates to square integrable coordinates. -/
theorem memLp_two_coords_metricScaled {d : ℕ} {V : Set (Vec d)} (m : Mat d)
    {X : Vec d → BlockVec d}
    (h1 : ∀ i, MemLp (fun x => (X x).1 i) 2 (volume.restrict V))
    (h2 : ∀ i, MemLp (fun x => (X x).2 i) 2 (volume.restrict V)) :
    (∀ i, MemLp (fun x => (matVecMul (matSqrt m) (X x).1) i) 2 (volume.restrict V)) ∧
      ∀ i, MemLp (fun x => (matVecMul (matSqrt m)⁻¹ (X x).2) i) 2 (volume.restrict V) := by
  have h := memLp_two_coords_blockMatVecMul
    (⟨matSqrt m, 0, 0, (matSqrt m)⁻¹⟩ : BlockMat d) h1 h2
  constructor
  · intro i
    have hfun : (fun x => (matVecMul (matSqrt m) (X x).1) i)
        = fun x =>
          (blockMatVecMul (⟨matSqrt m, 0, 0, (matSqrt m)⁻¹⟩ : BlockMat d) (X x)).1 i := by
      funext x
      simp [blockMatVecMul, matVecMul]
    rw [hfun]
    exact h.1 i
  · intro i
    have hfun : (fun x => (matVecMul (matSqrt m)⁻¹ (X x).2) i)
        = fun x =>
          (blockMatVecMul (⟨matSqrt m, 0, 0, (matSqrt m)⁻¹⟩ : BlockMat d) (X x)).2 i := by
      funext x
      simp [blockMatVecMul, matVecMul]
    rw [hfun]
    exact h.2 i

/-- The slotwise pullback bound for the gradient slot, with the square-integrability side
conditions supplied coordinatewise. -/
theorem partialSeminorm_pullback_fst_le_of_coords {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (m : Mat d) (hm : m.PosDef) (t : ℤ) (N : ℕ)
    (X : Vec d → BlockVec d)
    (h1 : ∀ i, MemLp (fun x => (X x).1 i) 2 (volume.restrict (HighContrast.adaptedCell q t)))
    (h2 : ∀ i, MemLp (fun x => (X x).2 i) 2 (volume.restrict (HighContrast.adaptedCell q t))) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul (matTranspose q) (X (matVecMul q y)).1) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq (matTranspose q * (matSqrt m)⁻¹)) *
        besovSeminorm t (cellAverageFamily q t fun x =>
          (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) := by
  obtain ⟨k1, k2⟩ := memLp_two_coords_metricScaled (V := HighContrast.adaptedCell q t) m h1 h2
  have hX : MemLp (fun x => blockVecDot
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) 1
      (volume.restrict (HighContrast.adaptedCell q t)) :=
    memLp_one_blockVecDot_self_of_coords (W := fun x =>
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) k1 k2
  have hXm : AEStronglyMeasurable
      (fun x => ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
      (volume.restrict (HighContrast.adaptedCell q t)) := by
    have hW1 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m) (X x).1)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k1 i).aestronglyMeasurable.aemeasurable
    have hW2 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m)⁻¹ (X x).2)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k2 i).aestronglyMeasurable.aemeasurable
    exact hW1.prodMk hW2
  exact partialSeminorm_pullback_fst_le q hq m hm t N X hX hXm

/-- The slotwise pullback bound for the flux slot, with the square-integrability side conditions
supplied coordinatewise. -/
theorem partialSeminorm_pullback_snd_le_of_coords {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (m : Mat d) (hm : m.PosDef) (t : ℤ) (N : ℕ)
    (X : Vec d → BlockVec d)
    (h1 : ∀ i, MemLp (fun x => (X x).1 i) 2 (volume.restrict (HighContrast.adaptedCell q t)))
    (h2 : ∀ i, MemLp (fun x => (X x).2 i) 2 (volume.restrict (HighContrast.adaptedCell q t))) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul q⁻¹ (X (matVecMul q y)).2) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq (q⁻¹ * matSqrt m)) *
        besovSeminorm t (cellAverageFamily q t fun x =>
          (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) := by
  obtain ⟨k1, k2⟩ := memLp_two_coords_metricScaled (V := HighContrast.adaptedCell q t) m h1 h2
  have hX : MemLp (fun x => blockVecDot
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) 1
      (volume.restrict (HighContrast.adaptedCell q t)) :=
    memLp_one_blockVecDot_self_of_coords (W := fun x =>
      (matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2)) k1 k2
  have hXm : AEStronglyMeasurable
      (fun x => ((matVecMul (matSqrt m) (X x).1, matVecMul (matSqrt m)⁻¹ (X x).2) : BlockVec d))
      (volume.restrict (HighContrast.adaptedCell q t)) := by
    have hW1 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m) (X x).1)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k1 i).aestronglyMeasurable.aemeasurable
    have hW2 : AEStronglyMeasurable (fun x => matVecMul (matSqrt m)⁻¹ (X x).2)
        (volume.restrict (HighContrast.adaptedCell q t)) := by
      rw [aestronglyMeasurable_iff_aemeasurable]
      rw [aemeasurable_pi_iff]
      intro i
      exact (k2 i).aestronglyMeasurable.aemeasurable
    exact hW1.prodMk hW2
  exact partialSeminorm_pullback_snd_le q hq m hm t N X hX hXm

end

end Homogenization.HighContrast.Multiscale
