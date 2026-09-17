import Homogenization.CoarseGraining.Definitions
import Homogenization.Ambient.CoefficientField
import Homogenization.PDE.Harmonic
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite splitting for CG response defects

Self-contained CG/Mathlib support for finite volume and integral decompositions.  The
same finite-volume facts are proved again in the response-weight file; this module repeats the short measure-theory layer
instead of importing any `HCPoly.Entry.*` module.
-/

namespace Homogenization.HighContrast.CG

open MeasureTheory
open scoped BigOperators

private theorem volume_piece_ne_top_of_subset {d : ℕ} {W V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)] (hsub : V ⊆ W) :
    volume V ≠ ⊤ := by
  have hW : volume W ≠ ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_ne_top (volumeMeasureOn W) Set.univ)
  exact MeasureTheory.measure_ne_top_of_subset hsub hW

private theorem measurable_iUnion_finset {d : ℕ} {ι : Type*}
    (F : Finset ι) {U : ι → Set (Vec d)}
    (hmeas : ∀ i ∈ F, MeasurableSet (U i)) :
    MeasurableSet (⋃ i ∈ F, U i) := by
  exact Finset.measurableSet_biUnion F hmeas

private theorem iUnion_finset_subset {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    (hsub : ∀ i ∈ F, U i ⊆ W) :
    (⋃ i ∈ F, U i) ⊆ W := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hiF, hxU⟩
  exact hsub i hiF hxU

theorem volume_eq_sum_add_remainder {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hmeas : ∀ i ∈ F, MeasurableSet (U i))
    (hsub : ∀ i ∈ F, U i ⊆ W) (hdisj : (F : Set ι).PairwiseDisjoint U) :
    (volume W).toReal = (∑ i ∈ F, (volume (U i)).toReal) +
      (volume (W \ ⋃ i ∈ F, U i)).toReal := by
  classical
  let S : Set (Vec d) := ⋃ i ∈ F, U i
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact measurable_iUnion_finset F hmeas
  have hSsub : S ⊆ W := by
    dsimp [S]
    exact iUnion_finset_subset F hsub
  have hWfin : volume W ≠ ⊤ :=
    volume_piece_ne_top_of_subset (W := W) (V := W) (fun _ hx => hx)
  have hSfin : volume S ≠ ⊤ :=
    volume_piece_ne_top_of_subset (W := W) (V := S) hSsub
  have hpieces_fin : ∀ i ∈ F, volume (U i) ≠ ⊤ := by
    intro i hi
    exact volume_piece_ne_top_of_subset (W := W) (V := U i) (hsub i hi)
  have hsum :
      volume.real S = ∑ i ∈ F, volume.real (U i) := by
    dsimp [S]
    exact MeasureTheory.measureReal_biUnion_finset hdisj hmeas hpieces_fin
  have hsplit :
      volume.real S + volume.real (W \ S) = volume.real W := by
    have hUnion : S ∪ W = W := Set.union_eq_self_of_subset_left hSsub
    simpa [S, hUnion] using
      MeasureTheory.measureReal_add_sdiff (μ := volume) hSmeas hSfin hWfin
  calc
    (volume W).toReal = volume.real S + volume.real (W \ S) := by
      simpa [Measure.real] using hsplit.symm
    _ = (∑ i ∈ F, (volume (U i)).toReal) +
        (volume (W \ ⋃ i ∈ F, U i)).toReal := by
      rw [hsum]
      rfl

theorem sum_volumeRatio_add_remainder_eq_one {d : ℕ} {ι : Type*}
    (F : Finset ι) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWvol : (volume W).toReal ≠ 0)
    (hmeas : ∀ i ∈ F, MeasurableSet (U i)) (hsub : ∀ i ∈ F, U i ⊆ W)
    (hdisj : (F : Set ι).PairwiseDisjoint U) :
    (∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal) +
      (volume (W \ ⋃ i ∈ F, U i)).toReal / (volume W).toReal = 1 := by
  classical
  have hsplit :=
    volume_eq_sum_add_remainder (F := F) (W := W) (U := U) hmeas hsub hdisj
  rw [← Finset.sum_div]
  field_simp [hWvol]
  linarith

end Homogenization.HighContrast.CG
