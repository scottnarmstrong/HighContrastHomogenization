/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.ClassCounterexample

/-!
# The boundedness hypothesis on the `H¹_a(V)` family is necessary

The energy slot of `MemH1a` is not of finite weighted energy on an unbounded `V`
(`exists_memH1a_sEnergyOn_eq_top`), and the same witness settles the function
slot.  `MemH1a` is an approximability condition: a globally smooth `u`
approximates itself at distance exactly `0`, whatever its growth, and the
coordinate function on `ℝ^d` is not of finite `L¹` mass.  So the `L¹` finiteness
of the function slot, the integrability of a member, and the pairing closure
that rests on them are all false without a hypothesis on `V`, and
`Bornology.IsBounded V` cannot be dropped from them.

The witness below exhibits exactly that and nothing else.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A closed half-space of `ℝ^d` has infinite Lebesgue measure in positive
dimension. -/
theorem volume_coordHalfspace_eq_top (hd : 0 < d) (i : Fin d) :
    volume (Set.univ.pi fun j : Fin d =>
      if j = i then Set.Ici (1 : ℝ) else (Set.univ : Set ℝ)) = ⊤ := by
  classical
  rw [volume_pi_pi]
  have hfac : ∀ j : Fin d,
      volume (if j = i then Set.Ici (1 : ℝ) else (Set.univ : Set ℝ)) = ⊤ := by
    intro j
    by_cases h : j = i
    · simp only [h]
      exact Real.volume_Ici
    · simp only [if_neg h]
      exact Real.volume_univ
  rw [Finset.prod_congr rfl fun j _ => hfac j]
  simp [Finset.prod_const, ENNReal.top_pow hd.ne']

/-- The coordinate function has infinite `L¹` mass on `ℝ^d`. -/
theorem lintegral_abs_coord_univ_eq_top (hd : 0 < d) (i : Fin d) :
    (∫⁻ x in (Set.univ : Set (Vec d)), ENNReal.ofReal |x i| ∂volume) = ⊤ := by
  classical
  set S : Set (Vec d) := Set.univ.pi fun j : Fin d =>
    if j = i then Set.Ici (1 : ℝ) else (Set.univ : Set ℝ) with hSdef
  have hSm : MeasurableSet S := by
    refine MeasurableSet.univ_pi fun j => ?_
    by_cases h : j = i
    · simp only [h]
      exact measurableSet_Ici
    · simp only [if_neg h]
      exact MeasurableSet.univ
  have hlow : volume S ≤ ∫⁻ x in S, ENNReal.ofReal |x i| ∂volume := by
    rw [← setLIntegral_one S]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hSm] with x hx
    have hxi : (1 : ℝ) ≤ x i := by
      have h := hx i (Set.mem_univ i)
      simpa only [hSdef, if_pos rfl, Set.mem_Ici] using! h
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal |x i| :=
          ENNReal.ofReal_le_ofReal (hxi.trans (le_abs_self _))
  have hmono : (∫⁻ x in S, ENNReal.ofReal |x i| ∂volume) ≤
      ∫⁻ x in (Set.univ : Set (Vec d)), ENNReal.ofReal |x i| ∂volume :=
    lintegral_mono' (Measure.restrict_mono (Set.subset_univ S) le_rfl) le_rfl
  refine top_le_iff.1 ?_
  calc (⊤ : ℝ≥0∞) = volume S := (volume_coordHalfspace_eq_top hd i).symm
    _ ≤ ∫⁻ x in S, ENNReal.ofReal |x i| ∂volume := hlow
    _ ≤ ∫⁻ x in (Set.univ : Set (Vec d)), ENNReal.ofReal |x i| ∂volume := hmono

/-- **The boundedness hypothesis of `lintegral_abs_ne_top_of_memH1a` cannot be
dropped.**  On `V = ℝ^d` the identity coefficient field and the coordinate
function lie in `MemH1a` while the `L¹` mass of the function slot is infinite;
so `integrableOn_of_memH1a_class` and the pairing closure that rests on it are
false without a hypothesis on `V`. -/
theorem exists_memH1a_lintegral_abs_eq_top (hd : 0 < d) :
    ∃ (b : CoeffField d) (u : Vec d → ℝ) (Du : Vec d → Vec d),
      MemH1a b (Set.univ : Set (Vec d)) u Du ∧
        (∫⁻ x in (Set.univ : Set (Vec d)),
          ENNReal.ofReal |u x| ∂volume) = ⊤ := by
  set i : Fin d := ⟨0, hd⟩ with hidef
  refine ⟨fun _ => (1 : Mat d), fun y => y i, fun _ => basisVec i, ?_,
    lintegral_abs_coord_univ_eq_top hd i⟩
  refine ⟨⟨(contDiff_coord i).continuous.aestronglyMeasurable,
    fun _ => aestronglyMeasurable_const⟩, ?_,
    fun _ => fun y : Vec d => y i, fun _ => contDiff_coord i, ?_, ?_⟩
  · have heq : (fun (x : Vec d) (j : Fin d) =>
        (fderiv ℝ (fun y : Vec d => y i) x) (basisVec j)) =
          fun _ : Vec d => basisVec i := funext fun x => smoothGrad_coord i x
    rw [← heq]
    exact HasWeakGradientOn.of_contDiff ((contDiff_coord i).of_le (by simp))
  · refine tendsto_const_nhds.congr fun n => ?_
    exact (h1sNormSqOn_eq_zero (b := fun _ => (1 : Mat d)) (fun x => by simp)
      (fun x => by simp [smoothGrad_coord i x])).symm
  · refine tendsto_const_nhds.congr fun n => ?_
    exact (skewFluxDualNorm_eq_zero (b := fun _ => (1 : Mat d))
      (fun x => by simp [smoothGrad_coord i x])).symm

end

end HighContrast
end Homogenization
