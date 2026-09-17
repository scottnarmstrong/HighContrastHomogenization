import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm
import HCPoly.Entry.Annealed.AlignedSubdivision

/-!
# Exact partition averaging for a cell average

The `3 ^ (n * d)` depth-`n` triadic subcells `adaptedCellAtCenter q (t - n) w`, indexed by
`w ∈ triadicIndexBox d n`, partition the adapted cell `HighContrast.adaptedCell q t` up to a null set,
and all have the same volume.  Hence the normalized sum of their averages of an integrable
function is the average over the parent cell.  This isolates the partition step used in the proof
of the response weak estimate `e.response.weak.estimate`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The triadic index box `triadicIndexBox d n` is exactly the set of depth-`n` index labels
whose standard-cell center lies in the generation-`t` centered cube. -/
theorem triadicIndexBox_eq_centerSet (t : ℤ) (n : ℕ) :
    (triadicIndexBox d n : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ |
        HighContrast.standardCellCenter (t - (n : ℤ)) w ∈ HighContrast.centeredCube d t} := by
  obtain ⟨b, hb⟩ : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
  have hm : (((3 ^ n - 1) / 2 : ℕ) : ℤ) = (b : ℤ) := by
    have hone : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  ext w
  change w ∈ triadicIndexBox d n ↔
    HighContrast.standardCellCenter (t - (n : ℤ)) w ∈ HighContrast.centeredCube d t
  rw [triadicIndexBox, Fintype.mem_piFinset]
  have hmem : HighContrast.standardCellCenter (t - (n : ℤ)) w ∈
      HighContrast.centeredCube d (t - (n : ℤ) + (n : ℤ)) ↔
        ∀ i, -(b : ℤ) ≤ w i ∧ w i ≤ (b : ℤ) :=
    Homogenization.HighContrast.Annealed.alignedCenter_mem_iff d (t - (n : ℤ)) n w b hb
  rw [show t - (n : ℤ) + (n : ℤ) = t by ring] at hmem
  rw [hmem]
  constructor
  · intro h i
    have hi := h i
    rw [Finset.mem_Icc, hm] at hi
    exact hi
  · intro h i
    rw [Finset.mem_Icc, hm]
    exact h i

omit [NeZero d] in
/-- The depth-`n` triadic subcells cover the adapted parent cell up to a null set. -/
theorem volume_adaptedCell_diff_iUnion_triadicIndexBox (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (n : ℕ) :
    volume (HighContrast.adaptedCell q t \
        ⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) = 0 := by
  have hnull : volume (HighContrast.adaptedCell q (t - (n : ℤ) + (n : ℤ)) \
      ⋃ w ∈ {w : Fin d → ℤ |
        HighContrast.standardCellCenter (t - (n : ℤ)) w ∈
          HighContrast.centeredCube d (t - (n : ℤ) + (n : ℤ))},
        adaptedCellAtCenter q (t - (n : ℤ)) w) = 0 :=
    (Homogenization.HighContrast.Annealed.aligned_adapted_partition (d := d) q hq (t - (n : ℤ)) n).2.2
  rw [show t - (n : ℤ) + (n : ℤ) = t by ring] at hnull
  rw [← triadicIndexBox_eq_centerSet t n] at hnull
  exact hnull

/-- Exact partition averaging: the normalized sum of the averages of an integrable function over
the `3 ^ (n * d)` depth-`n` triadic subcells equals the average over the adapted parent cell.
This is the partition step in the proof of the response weak estimate
`e.response.weak.estimate`. -/
theorem avsum_volumeAverage_eq (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    {f : Vec d → ℝ} (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      = volumeAverage (HighContrast.adaptedCell q t) f := by
  classical
  have _ : NeZero d := inferInstance
  set U : Set (Vec d) := HighContrast.adaptedCell q t with hU
  set V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w with hV
  have hUreal : (volume U).toReal = |q.det| * ((3 : ℝ) ^ t) ^ d :=
    Geometry.volume_adaptedCell_toReal q t
  have hVmeas : ∀ w, MeasurableSet (V w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
  have hVreal : ∀ w, (volume (V w)).toReal = |q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
    intro w
    rw [hV, Geometry.volume_adaptedCellAtCenter]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
  have hVconst : ∀ w, (volume (V w)).toReal = (volume (V 0)).toReal := by
    intro w; rw [hVreal w, hVreal 0]
  have hsub : ∀ w ∈ triadicIndexBox d n, V w ⊆ U := by
    intro w hw
    rw [hU, hV]
    exact adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVint : ∀ w ∈ triadicIndexBox d n, IntegrableOn f (V w) :=
    fun w hw => hf.mono_set (hsub w hw)
  have hdisj : Set.Pairwise (↑(triadicIndexBox d n) : Set (Fin d → ℤ))
      (Function.onFun Disjoint V) := by
    intro a _ b _ hab
    exact Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hab
  have hunion : ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x
      = ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x :=
    integral_biUnion_finset _ (fun w _ => hVmeas w) hdisj hVint
  have hcover : volume (U \ ⋃ w ∈ triadicIndexBox d n, V w) = 0 := by
    rw [hU, hV]
    exact volume_adaptedCell_diff_iUnion_triadicIndexBox q hq t n
  have hae : U =ᵐ[volume] (⋃ w ∈ triadicIndexBox d n, V w) := by
    rw [ae_eq_set]
    refine ⟨hcover, ?_⟩
    have hsubU : (⋃ w ∈ triadicIndexBox d n, V w) ⊆ U :=
      Set.iUnion₂_subset (fun w hw => hsub w hw)
    rw [Set.sdiff_eq_empty.mpr hsubU, measure_empty]
  have hInt : ∫ x in U, f x = ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x :=
    setIntegral_congr_set hae
  have hNcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d := card_triadicIndexBox n
  have hprod : ((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal = (volume U).toReal := by
    rw [hNcard, hVreal 0, hUreal]
    have h3 : (3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ)) = (3 : ℝ) ^ t := by
      rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast (3 : ℝ) n).symm,
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    calc ((3 : ℝ) ^ n) ^ d * (|q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d)
        = |q.det| * ((3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ))) ^ d := by rw [mul_pow]; ring
      _ = |q.det| * ((3 : ℝ) ^ t) ^ d := by rw [h3]
  have hcoef : ((triadicIndexBox d n).card : ℝ)⁻¹ * ((volume (V 0)).toReal)⁻¹
      = (((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal)⁻¹ := by
    rw [mul_inv]
  calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, volumeAverage (V w) f
      = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (volume (V 0)).toReal⁻¹ * ∫ x in V w, f x := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro w _
        rw [volumeAverage, hVconst w]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ((volume (V 0)).toReal⁻¹ * ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x) := by
        rw [← Finset.mul_sum]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ((volume (V 0)).toReal⁻¹ * ∫ x in U, f x) := by
        rw [← hunion, hInt]
    _ = (((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal)⁻¹ * ∫ x in U, f x := by
        rw [← mul_assoc, hcoef]
    _ = volumeAverage U f := by
        rw [hprod, volumeAverage]

end

end Homogenization.HighContrast.Multiscale
