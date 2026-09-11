/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridRows

/-!
# Volume budget for the reverse hybrid filling

Any finite collection of selected cells lies in the uncovered strip.  Their
total volume therefore inherits the packing-fraction estimate with the outer
target as denominator.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The selected rows of the hybrid filling have total relative volume at most
the relative volume of the uncovered strip. -/
theorem sum_relative_volume_hybridFilling_le_strip {q q' : Mat d}
    (hd : 1 ≤ d) (hq : q.PosDef) (hq' : q'.PosDef)
    {n l : ℤ} (y : Vec d) {R : Finset ℤ}
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n
      (hybridStrip q' n (adaptedCellTranslate q (n + l) y)) r) :
    ∑ r ∈ R, ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
        (volume (adaptedCellTranslate q (n + l) y)).toReal ≤
      2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
        (3 : ℝ) ^ (-(l : ℤ)) := by
  classical
  let W : Set (Vec d) := adaptedCellTranslate q (n + l) y
  let Strip : Set (Vec d) := hybridStrip q' n W
  have hmem : ∀ r : ℤ, ∀ w ∈ Z r, w ∈ fillingIndex q n Strip r := by
    intro r w hw
    have hw' : w ∈ (↑(Z r) : Set (Fin d → ℤ)) := hw
    simpa only [Strip, W, hZ r] using hw'
  let I : Finset ((_ : ℤ) × (Fin d → ℤ)) := R.sigma Z
  have hdisj : (↑I : Set ((_ : ℤ) × (Fin d → ℤ))).PairwiseDisjoint
      fun x => adaptedCellAt q x.1 x.2 := by
    intro x hx yy hyy hne
    change x ∈ R.sigma Z at hx
    change yy ∈ R.sigma Z at hyy
    rw [Finset.mem_sigma] at hx hyy
    refine disjoint_of_mem_fillingIndex hq (hmem _ _ hx.2) (hmem _ _ hyy.2) ?_
    intro hpair
    exact hne (Sigma.ext (congrArg Prod.fst hpair)
      (heq_of_eq (congrArg Prod.snd hpair)))
  have hmeas : ∀ x ∈ I, MeasurableSet (adaptedCellAt q x.1 x.2) := fun x _ =>
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq x.1 x.2).isOpen.measurableSet
  have hsub : (⋃ x ∈ I, adaptedCellAt q x.1 x.2) ⊆ Strip := by
    refine Set.iUnion₂_subset fun x hx => ?_
    change x ∈ R.sigma Z at hx
    rw [Finset.mem_sigma] at hx
    exact adaptedCellAt_subset_of_mem_fillingIndex (hmem _ _ hx.2)
  have hsum : ∑ x ∈ I, volume (adaptedCellAt q x.1 x.2) ≤ volume Strip := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  have hstrip : volume Strip ≤
      ENNReal.ofReal (2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
        (3 : ℝ) ^ (-(l : ℤ))) * volume W := by
    simpa only [Strip, W] using volume_hybridStrip_le_gridRatio hd hq hq' n l y
  have hWtop : volume W ≠ ⊤ := volume_adaptedCellTranslate_ne_top q (n + l) y
  have hWpos : (0 : ℝ) < (volume W).toReal :=
    ENNReal.toReal_pos (volume_adaptedCellTranslate_ne_zero hq (n + l) y) hWtop
  have hcelltop : ∀ x : (_ : ℤ) × (Fin d → ℤ),
      volume (adaptedCellAt q x.1 x.2) ≠ ⊤ := by
    intro x
    rw [adaptedCellAt_eq_adaptedCellTranslate]
    exact volume_adaptedCellTranslate_ne_top q x.1 _
  have hcoeff0 : 0 ≤ 2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
      (3 : ℝ) ^ (-(l : ℤ)) := by
    rw [gridRatio]
    positivity
  have hreal : ∑ x ∈ I, (volume (adaptedCellAt q x.1 x.2)).toReal ≤
      (2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
        (3 : ℝ) ^ (-(l : ℤ))) * (volume W).toReal := by
    have hle := hsum.trans hstrip
    have htop : ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
            (3 : ℝ) ^ (-(l : ℤ))) * volume W ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWtop
    have hle' := ENNReal.toReal_mono htop hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoeff0,
      ENNReal.toReal_sum fun x _ => hcelltop x] at hle'
    exact hle'
  have hsplit : ∑ r ∈ R, ∑ w ∈ Z r,
      (volume (adaptedCellAt q r w)).toReal / (volume W).toReal =
        (∑ x ∈ I, (volume (adaptedCellAt q x.1 x.2)).toReal) /
          (volume W).toReal := by
    change _ = (∑ x ∈ R.sigma Z,
      (volume (adaptedCellAt q x.1 x.2)).toReal) / (volume W).toReal
    rw [Finset.sum_div, Finset.sum_sigma']
  rw [show adaptedCellTranslate q (n + l) y = W by rfl, hsplit,
    div_le_iff₀ hWpos]
  exact hreal

/-- The packed row occupies at least one minus the relative boundary-strip
volume of its target. -/
theorem one_sub_le_sum_relative_volume_hybridPacking {q q' : Mat d}
    (hd : 1 ≤ d) (hq : q.PosDef) (hq' : q'.PosDef)
    {n l : ℤ} (y : Vec d) {Zp : Finset (Fin d → ℤ)}
    (hZp : ↑Zp = hybridPackingIndex q' n
      (adaptedCellTranslate q (n + l) y)) :
    1 - 2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
        (3 : ℝ) ^ (-(l : ℤ)) ≤
      ∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal /
        (volume (adaptedCellTranslate q (n + l) y)).toReal := by
  classical
  let W : Set (Vec d) := adaptedCellTranslate q (n + l) y
  let U : Set (Vec d) := ⋃ w ∈ Zp, adaptedCellAt q' n w
  let Strip : Set (Vec d) := hybridStrip q' n W
  have hmem : ∀ w ∈ Zp, w ∈ hybridPackingIndex q' n W := by
    intro w hw
    rw [← hZp]
    exact Finset.mem_coe.mpr hw
  have hdisj : (↑Zp : Set (Fin d → ℤ)).PairwiseDisjoint
      fun w => adaptedCellAt q' n w := by
    intro w _ v _ hwv
    exact Recurrence.disjoint_adaptedCellAt hq' n (by simpa using hwv)
  have hmeas : ∀ w ∈ Zp, MeasurableSet (adaptedCellAt q' n w) := fun w _ =>
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq' n w).isOpen.measurableSet
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    exact Finset.measurableSet_biUnion Zp hmeas
  have hUsub : U ⊆ W := by
    dsimp only [U]
    refine Set.iUnion₂_subset fun w hw => ?_
    exact adaptedCellAt_subset_of_mem_fillingIndex (hmem w hw)
  have hsumU : volume U = ∑ w ∈ Zp, volume (adaptedCellAt q' n w) := by
    dsimp only [U]
    exact measure_biUnion_finset hdisj hmeas
  have hStripEq : Strip = W \ U := by
    dsimp only [Strip, W, U, hybridStrip]
    rw [← Finset.set_biUnion_coe, hZp]
  have hdecomp : volume Strip + volume U = volume W := by
    have h := measure_diff_add_inter (μ := volume) W hUmeas
    rw [Set.inter_eq_right.mpr hUsub] at h
    rw [hStripEq]
    exact h
  have hstrip : volume Strip ≤
      ENNReal.ofReal (2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
        (3 : ℝ) ^ (-(l : ℤ))) * volume W := by
    simpa only [Strip, W] using volume_hybridStrip_le_gridRatio hd hq hq' n l y
  have hWtop : volume W ≠ ⊤ := volume_adaptedCellTranslate_ne_top q (n + l) y
  have hWpos : (0 : ℝ) < (volume W).toReal :=
    ENNReal.toReal_pos (volume_adaptedCellTranslate_ne_zero hq (n + l) y) hWtop
  have hUtop : volume U ≠ ⊤ := ne_top_of_le_ne_top hWtop (measure_mono hUsub)
  have hStriptop : volume Strip ≠ ⊤ := ne_top_of_le_ne_top hWtop
    (measure_mono hybridStrip_subset)
  have hcoeff0 : 0 ≤ 2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
      (3 : ℝ) ^ (-(l : ℤ)) := by
    rw [gridRatio]
    positivity
  have hrealdecomp : (volume Strip).toReal + (volume U).toReal =
      (volume W).toReal := by
    rw [← ENNReal.toReal_add hStriptop hUtop, hdecomp]
  have hrealstrip : (volume Strip).toReal ≤
      (2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
        (3 : ℝ) ^ (-(l : ℤ))) * (volume W).toReal := by
    have htop : ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * gridRatio q q' *
            (3 : ℝ) ^ (-(l : ℤ))) * volume W ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWtop
    have h := ENNReal.toReal_mono htop hstrip
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoeff0] at h
  have hUreal : (volume U).toReal =
      ∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal := by
    rw [hsumU, ENNReal.toReal_sum]
    intro w _
    rw [adaptedCellAt_eq_adaptedCellTranslate]
    exact volume_adaptedCellTranslate_ne_top q' n _
  rw [show adaptedCellTranslate q (n + l) y = W by rfl, ← Finset.sum_div,
    ← hUreal, le_div_iff₀ hWpos]
  nlinarith only [hrealdecomp, hrealstrip]

end

end Transport
end HighContrast
end Homogenization
