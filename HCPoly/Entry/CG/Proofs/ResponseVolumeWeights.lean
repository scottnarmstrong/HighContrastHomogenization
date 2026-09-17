import Homogenization.CoarseGraining.Definitions
import Homogenization.Ambient.CoefficientField
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Volume weights for CG response sums

Self-contained CG/Mathlib support for the relative-volume weights appearing in the
countable response summability statement.
-/

namespace Homogenization.HighContrast.CG

open MeasureTheory BigOperators

theorem volume_piece_ne_top_of_subset {d : ℕ} {W V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)] (hsub : V ⊆ W) :
    volume V ≠ ⊤ := by
  have hW : volume W ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_ne_top (volumeMeasureOn W) Set.univ)
  exact MeasureTheory.measure_ne_top_of_subset hsub hW

private theorem pairwiseDisjoint_subtype_finset {d : ℕ} {ι : Type*} {s : Set ι}
    {U : ι → Set (Vec d)} (hdisj : s.PairwiseDisjoint U) (F : Finset s) :
    (F : Set s).PairwiseDisjoint fun i : s => U i.1 := by
  intro i _hi j _hj hij
  exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))

theorem sum_volumeRatio_le_one {d : ℕ} {ι : Type*} {s : Set ι}
    {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hmeas : ∀ i ∈ s, MeasurableSet (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (F : Finset s) :
    ∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal ≤ 1 := by
  classical
  have hWfin : volume W ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_ne_top (volumeMeasureOn W) Set.univ)
  by_cases hWzero : (volume W).toReal = 0
  · have hWnull : volume W = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (volume W)).mp hWzero with h | h
      · exact h
      · exact (hWfin h).elim
    have hterm_zero :
        ∀ i : s, (volume (U i)).toReal / (volume W).toReal = 0 := by
      intro i
      have hUi_null : volume (U i.1) = 0 :=
        MeasureTheory.measure_mono_null (hsub i.1 i.2) hWnull
      simp [hWzero, hUi_null]
    simp [hterm_zero]
  · have hWpos : 0 < (volume W).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hWzero)
    have hfinite :
        ∀ i ∈ F, volume (U i.1) ≠ ⊤ := by
      intro i _hi
      exact volume_piece_ne_top_of_subset (W := W) (V := U i.1) (hsub i.1 i.2)
    have hmeasF :
        ∀ i ∈ F, MeasurableSet (U i.1) := by
      intro i _hi
      exact hmeas i.1 i.2
    have hsum_eq :
        volume.real (⋃ i ∈ F, U i.1) =
          ∑ i ∈ F, volume.real (U i.1) :=
      MeasureTheory.measureReal_biUnion_finset
        (pairwiseDisjoint_subtype_finset hdisj F) hmeasF hfinite
    have hUnionSub : (⋃ i ∈ F, U i.1) ⊆ W := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hiF, hxUi⟩
      exact hsub i.1 i.2 hxUi
    have hsum_le :
        ∑ i ∈ F, (volume (U i.1)).toReal ≤ (volume W).toReal := by
      calc
        ∑ i ∈ F, (volume (U i.1)).toReal
            = volume.real (⋃ i ∈ F, U i.1) := by
              simpa [Measure.real] using hsum_eq.symm
        _ ≤ volume.real W :=
              MeasureTheory.measureReal_mono hUnionSub hWfin
        _ = (volume W).toReal := rfl
    rw [← Finset.sum_div]
    exact (div_le_iff₀ hWpos).mpr (by simpa using hsum_le)

theorem summable_volumeRatio {d : ℕ} {ι : Type*} {s : Set ι}
    {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hmeas : ∀ i ∈ s, MeasurableSet (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) :
    Summable (fun i : s => (volume (U i)).toReal / (volume W).toReal) := by
  refine summable_of_sum_le (c := 1) ?_ ?_
  · intro i
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · intro F
    simpa using sum_volumeRatio_le_one hmeas hsub hdisj F

end Homogenization.HighContrast.CG
