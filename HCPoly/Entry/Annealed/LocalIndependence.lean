import HCPoly.Entry.Setup.UnitRange
import HCPoly.Entry.Setup.Stationarity
import Homogenization.Geometry.Translation
import Mathlib.Probability.Independence.Basic

/-!
# Local independence on the coefficient sigma-fields

This file works directly with the carrier `CoeffSpace` and the
support-generated sigma-fields `coeffSigma`.  It deliberately does not coerce
the law to an AKL fixed-ellipticity carrier.
-/

open Homogenization.HighContrast (CoeffSpace IsLocalTest UnitSeparated coeffPairing coeffSigma)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory ProbabilityTheory

noncomputable section

theorem coeffSigma_mono
    {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V) :
    coeffSigma d U ≤ coeffSigma d V := by
  unfold coeffSigma
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨e, e', φ, hφ, t, ht, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, ⟨hφ.contDiff, hφ.hasCompactSupport, hφ.tsupport_subset.trans hUV⟩,
      t, ht, rfl⟩

theorem coeffSigma_le_global
    {d : ℕ} (U : Set (Vec d)) :
    coeffSigma d U ≤ (inferInstance : MeasurableSpace (CoeffSpace d)) :=
  coeffSigma_mono (Set.subset_univ U)

theorem measurable_coeffPairing_local
    {d : ℕ} {U : Set (Vec d)} (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ : IsLocalTest U φ) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d U) inferInstance
      (coeffPairing e e' φ) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom ⟨e, e', φ, hφ, t, ht, rfl⟩

private theorem unitSeparated_biUnion_right {d : ℕ} {ι : Type*}
    {U : Set (Vec d)} {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, UnitSeparated U (V i)) :
    UnitSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact h i hi hx hyi

private theorem measurableSet_biInter_coeffSigma_biUnion {d : ℕ} {ι : Type*}
    {U : ι → Set (Vec d)}
    {f : ι → Set (CoeffSpace d)} {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (CoeffSpace d) (coeffSigma d (U i)) (f i)) :
    @MeasurableSet (CoeffSpace d)
      (coeffSigma d (⋃ i ∈ s, U i)) (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (CoeffSpace d)
            (coeffSigma d (⋃ j ∈ insert i s, U j)) (f i) :=
        (coeffSigma_mono hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (CoeffSpace d)
            (coeffSigma d (⋃ j ∈ insert i s, U j)) (⋂ j ∈ s, f j) :=
        (coeffSigma_mono hsubset_s)
          (⋂ j ∈ s, f j) (ih fun j hj => hf j (by simp [hj]))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

theorem iIndep_coeffSigma_of_isUnitRangeLaw
    {d : ℕ} {ι : Type*} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hP : IsUnitRangeLaw P) (U : ι → Set (Vec d))
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => UnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => coeffSigma d (U i)) P := by
  classical
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ => hU j
      have hsep_union : UnitSeparated (U i) (⋃ j ∈ s, U j) := by
        refine unitSeparated_biUnion_right (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (CoeffSpace d) (coeffSigma d (⋃ j ∈ s, U j))
            (⋂ j ∈ s, f j) :=
        measurableSet_biInter_coeffSigma_biUnion (U := U)
          (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := by
        exact (ProbabilityTheory.Indep_iff
          (coeffSigma d (U i)) (coeffSigma d (⋃ j ∈ s, U j)) P).1
            (hP (U i) (⋃ j ∈ s, U j) (hU i) hUnion hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        P (⋂ j ∈ insert i s, f j) = P (f i ∩ ⋂ j ∈ s, f j) := by simp
        _ = P (f i) * P (⋂ j ∈ s, f j) := h_inter
        _ = P (f i) * ∏ j ∈ s, P (f j) := by
          rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, P (f j) := by simp [Finset.prod_insert, hi]

theorem iIndepFun_of_coeffSigma_measurable
    {d : ℕ} {ι : Type*} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hP : IsUnitRangeLaw P) (U : ι → Set (Vec d))
    (hU : ∀ i, MeasurableSet (U i)) {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (X : ∀ i, CoeffSpace d → β i)
    (hX : ∀ i, @Measurable (CoeffSpace d) (β i) (coeffSigma d (U i))
      inferInstance (X i))
    (hsep : Pairwise fun i j => UnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndepFun X P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  exact (ProbabilityTheory.iIndep_iff (fun i => coeffSigma d (U i)) P).1
    (iIndep_coeffSigma_of_isUnitRangeLaw (P := P) hP U hU hsep) s
    (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

end

end Homogenization.HighContrast.Annealed
