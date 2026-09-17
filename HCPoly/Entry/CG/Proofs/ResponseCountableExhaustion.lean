import HCPoly.Entry.CG.Proofs.ResponseVolumeWeights
import HCPoly.Entry.CG.Proofs.ResponseFiniteSplitting
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Countable exhaustion support for CG response sums

This file supplies the measure-theoretic countable-exhaustion facts used by the
countable scalar response statement.  The route is finite-stage splitting plus the
ordinary `HasSum` limit over finite subsets; no response or coarse matrix is formed
on the non-open remainder.
-/

namespace Homogenization.HighContrast.CG

open MeasureTheory Function Filter
open scoped BigOperators

private theorem subtype_iUnion_eq {α ι : Type*} {s : Set ι} {U : ι → Set α} :
    (⋃ i : Subtype (fun j : ι => j ∈ s), U (i : ι)) =
      (⋃ i : ι, ⋃ _hi : i ∈ s, U i) := by
  ext x
  simp

private theorem iUnion_subtype_subset {d : ℕ} {ι : Type*} {s : Set ι}
    {W : Set (Vec d)} {U : ι → Set (Vec d)}
    (hsub : ∀ i ∈ s, U i ⊆ W) :
    (⋃ i : Subtype (fun j : ι => j ∈ s), U (i : ι)) ⊆ W := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  exact hsub (i : ι) i.2 hxi

private theorem pairwiseDisjoint_subtype {d : ℕ} {ι : Type*} {s : Set ι}
    {U : ι → Set (Vec d)} (hdisj : s.PairwiseDisjoint U) :
    Pairwise (Disjoint on fun i : s => U (i : ι)) := by
  intro i j hij
  exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))

/-- The relative volumes of a countable disjoint family exhausting `W` up to a null set
sum to one.  This is independent of ellipticity and response values. -/
theorem tsum_volumeRatio_eq_one {d : ℕ} {ι : Type*} {s : Set ι} (hs : s.Countable)
    {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWvol : (volume W).toReal ≠ 0)
    (hmeas : ∀ i ∈ s, MeasurableSet (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0) :
    ∑' i : s, (volume (U i.1)).toReal / (volume W).toReal = 1 := by
  classical
  have : Countable s := hs.to_subtype
  let S : Set (Vec d) := ⋃ i : Subtype (fun j : ι => j ∈ s), U (i : ι)
  have hSsub : S ⊆ W := by
    dsimp [S]
    exact iUnion_subtype_subset hsub
  have hSmeas : ∀ i : s, MeasurableSet (U (i : ι)) := fun i => hmeas (i : ι) i.2
  have hSdisj : Pairwise (Disjoint on fun i : s => U (i : ι)) :=
    pairwiseDisjoint_subtype hdisj
  have hSnull : volume (W \ S) = 0 := by
    dsimp [S]
    simpa [subtype_iUnion_eq] using hnull
  have hSvolume : volume S = volume W := by
    apply le_antisymm
    · exact measure_mono hSsub
    · calc
        volume W ≤ volume (S ∪ (W \ S)) := by
          refine measure_mono ?_
          intro x hx
          by_cases hxS : x ∈ S
          · exact Or.inl hxS
          · exact Or.inr ⟨hx, hxS⟩
        _ ≤ volume S + volume (W \ S) := measure_union_le S (W \ S)
        _ = volume S := by simp [hSnull]
  have hUnionMeasure : volume S = ∑' i : s, volume (U (i : ι)) := by
    dsimp [S]
    exact MeasureTheory.measure_iUnion hSdisj hSmeas
  have hfinite : ∀ i : s, volume (U (i : ι)) ≠ ⊤ := fun i =>
    volume_piece_ne_top_of_subset (W := W) (V := U (i : ι)) (hsub (i : ι) i.2)
  have hvolReal : (volume W).toReal = ∑' i : s, (volume (U (i : ι))).toReal := by
    calc
      (volume W).toReal = (volume S).toReal := by rw [hSvolume]
      _ = (∑' i : s, volume (U i.1)).toReal := by rw [hUnionMeasure]
      _ = ∑' i : s, (volume (U (i : ι))).toReal :=
          ENNReal.tsum_toReal_eq hfinite
  calc
    ∑' i : s, (volume (U i.1)).toReal / (volume W).toReal
        = (∑' i : s, (volume (U (i : ι))).toReal) / (volume W).toReal := by
          rw [tsum_div_const]
    _ = (volume W).toReal / (volume W).toReal := by rw [hvolReal]
    _ = 1 := div_self hWvol

/-- Along finite subfamilies of a countable null exhaustion, the normalized uncovered
volume tends to zero. -/
theorem tendsto_remainder_volumeRatio_zero {d : ℕ} {ι : Type*} {s : Set ι}
    (hs : s.Countable) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWvol : (volume W).toReal ≠ 0)
    (hmeas : ∀ i ∈ s, MeasurableSet (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0) :
    Tendsto
      (fun F : Finset s =>
        (volume (W \ ⋃ i ∈ F, U (i : ι))).toReal / (volume W).toReal)
      atTop (nhds 0) := by
  classical
  let w : s → ℝ := fun i => (volume (U (i : ι))).toReal / (volume W).toReal
  have hsum : Summable w :=
    summable_volumeRatio hmeas hsub hdisj
  have htsum : ∑' i : s, w i = 1 := by
    dsimp [w]
    exact tsum_volumeRatio_eq_one hs hWvol hmeas hsub hdisj hnull
  have hweights :
      Tendsto (fun F : Finset s => ∑ i ∈ F, w i) atTop (nhds 1) := by
    have hhas := hsum.hasSum
    rw [htsum] at hhas
    simpa [HasSum] using hhas
  have hremainder_eq :
      ∀ F : Finset s,
        (volume (W \ ⋃ i ∈ F, U (i : ι))).toReal / (volume W).toReal =
          1 - ∑ i ∈ F, w i := by
    intro F
    have hmeasF : ∀ i ∈ F, MeasurableSet (U (i : ι)) := fun i _hi => hmeas (i : ι) i.2
    have hsubF : ∀ i ∈ F, U (i : ι) ⊆ W := fun i _hi => hsub (i : ι) i.2
    have hdisjF : (F : Set s).PairwiseDisjoint fun i : s => U (i : ι) := by
      intro i _hi j _hj hij
      exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
    have hsplit :=
      sum_volumeRatio_add_remainder_eq_one (F := F) (W := W)
        (U := fun i : s => U (i : ι)) hWvol hmeasF hsubF hdisjF
    dsimp [w] at hsplit ⊢
    linarith
  have hdiff :
      Tendsto (fun F : Finset s => 1 - ∑ i ∈ F, w i) atTop (nhds (1 - 1)) :=
    tendsto_const_nhds.sub hweights
  have hdiff_zero :
      Tendsto (fun F : Finset s => 1 - ∑ i ∈ F, w i) atTop (nhds 0) := by
    simpa using hdiff
  exact hdiff_zero.congr' (Eventually.of_forall fun F => (hremainder_eq F).symm)

end Homogenization.HighContrast.CG
