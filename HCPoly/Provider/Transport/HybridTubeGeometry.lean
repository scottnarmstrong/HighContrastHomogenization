/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridPacking

/-!
# Coordinate tubes around adapted cells

The tube estimate in `l.two.grid.whitney` is reduced to the
coordinate slabs around a parallelepiped.  The estimates here cover the part
outside a cell as well as the inner boundary layer already used by the Whitney
filling.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem volume_outer_slabLine_le {j : ℤ} {t : ℝ} (ht : 0 ≤ t) :
    volume (Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
        ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t) ∩
      {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |s|}) ≤ ENNReal.ofReal (2 * t) := by
  have hsub : Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
        ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t) ∩
      {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |s|} ⊆
      Set.Icc (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
          (-((1 : ℝ) / 2 * (3 : ℝ) ^ j)) ∪
        Set.Icc ((1 : ℝ) / 2 * (3 : ℝ) ^ j)
          ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t) := by
    rintro s ⟨⟨hlo, hhi⟩, habs⟩
    rw [Set.mem_ofPred_eq] at habs
    rcases le_or_gt 0 s with hs | hs
    · exact Or.inr ⟨by rwa [abs_of_nonneg hs] at habs, hhi.le⟩
    · refine Or.inl ⟨hlo.le, ?_⟩
      rw [abs_of_neg hs] at habs
      linarith only [habs]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_Icc, Real.volume_Icc]
  have hlo : -((1 : ℝ) / 2 * (3 : ℝ) ^ j) -
      (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t)) = t := by ring
  have hhi : (1 : ℝ) / 2 * (3 : ℝ) ^ j + t -
      (1 : ℝ) / 2 * (3 : ℝ) ^ j = t := by ring
  rw [hlo, hhi, ← ENNReal.ofReal_add ht ht]
  ring_nf
  exact le_rfl

/-- The bilateral coordinate layer of a centered triadic cube has volume at
most its thickness times the area of the expanded coordinate faces. -/
theorem volume_outer_layer_centeredCube_le [NeZero d] (j : ℤ) {t : ℝ}
    (ht : 0 ≤ t) :
    volume {z : Vec d |
        (∀ k, |z k| < (1 / 2 : ℝ) * (3 : ℝ) ^ j + t) ∧
          ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |z i|} ≤
      ENNReal.ofReal
        (2 * (d : ℝ) * t * ((3 : ℝ) ^ j + 2 * t) ^ (d - 1)) := by
  classical
  set L : ℝ := (3 : ℝ) ^ j + 2 * t with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hcover : {z : Vec d |
      (∀ k, |z k| < (1 / 2 : ℝ) * (3 : ℝ) ^ j + t) ∧
        ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |z i|} ⊆
      ⋃ i : Fin d, Set.univ.pi fun k : Fin d =>
        if k = i then
          Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
              ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t) ∩
            {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |s|}
        else Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
          ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t) := by
    rintro z ⟨hz, i, hi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [Set.mem_univ_pi]
    intro k
    have hk := hz k
    rw [abs_lt] at hk
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl]
      exact ⟨⟨hk.1, hk.2⟩, hi⟩
    · rw [if_neg hki]
      exact ⟨hk.1, hk.2⟩
  have hrow : ∀ i : Fin d,
      volume (Set.univ.pi fun k : Fin d =>
        if k = i then
          Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
              ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t) ∩
            {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |s|}
        else Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
          ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t)) ≤
        ENNReal.ofReal (2 * t * L ^ (d - 1)) := by
    intro i
    rw [volume_pi, MeasureTheory.Measure.pi_pi]
    have hfac : ∀ k ∈ (Finset.univ : Finset (Fin d)),
        volume (if k = i then
          Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
              ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t) ∩
            {s : ℝ | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |s|}
        else Set.Ioo (-((1 : ℝ) / 2 * (3 : ℝ) ^ j + t))
          ((1 : ℝ) / 2 * (3 : ℝ) ^ j + t)) ≤
        if k = i then ENNReal.ofReal (2 * t) else ENNReal.ofReal L := by
      intro k _
      by_cases hki : k = i
      · subst hki
        rw [if_pos rfl, if_pos rfl]
        exact volume_outer_slabLine_le (j := j) ht
      · rw [if_neg hki, if_neg hki, Real.volume_Ioo, hL]
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        ring
    refine (Finset.prod_le_prod' hfac).trans_eq ?_
    have hprod : (∏ k : Fin d,
        if k = i then ENNReal.ofReal (2 * t) else ENNReal.ofReal L) =
        ENNReal.ofReal (2 * t) * ENNReal.ofReal L ^ (d - 1) := by
      calc
        (∏ k : Fin d,
            if k = i then ENNReal.ofReal (2 * t) else ENNReal.ofReal L) =
            (if i = i then ENNReal.ofReal (2 * t) else ENNReal.ofReal L) *
              ∏ k ∈ (Finset.univ : Finset (Fin d)).erase i,
                (if k = i then ENNReal.ofReal (2 * t) else ENNReal.ofReal L) :=
          (Finset.mul_prod_erase (Finset.univ : Finset (Fin d))
            (fun k => if k = i then ENNReal.ofReal (2 * t) else ENNReal.ofReal L)
            (Finset.mem_univ i)).symm
        _ = ENNReal.ofReal (2 * t) *
              ∏ _k ∈ (Finset.univ : Finset (Fin d)).erase i, ENNReal.ofReal L := by
            rw [if_pos rfl]
            congr 1
            refine Finset.prod_congr rfl fun k hk => ?_
            rw [if_neg (Finset.ne_of_mem_erase hk)]
        _ = ENNReal.ofReal (2 * t) * ENNReal.ofReal L ^ (d - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin]
    rw [hprod, ← ENNReal.ofReal_pow hL0, ← ENNReal.ofReal_mul (by positivity)]
  refine (measure_mono hcover).trans ((measure_iUnion_fintype_le volume _).trans ?_)
  refine (Finset.sum_le_sum fun i _ => hrow i).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
  congr 1
  rw [hL]
  ring

/-- Points outside a scale-`n` adapted cell that share a scale-`c` cell of a
second grid with a point inside it occupy a coordinate tube around its faces. -/
theorem volume_cellNeighbor_outside_le [NeZero d] {p q : Mat d} (hp : p.PosDef)
    {c n : ℤ} (hcn : c ≤ n) (w : Fin d → ℤ) :
    volume {x : Vec d | x ∉ adaptedCellAt p n w ∧
        ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
          (adaptedCellAt q c v ∩ adaptedCellAt p n w).Nonempty} ≤
      ENNReal.ofReal
          (2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
            (1 + 6 * Real.sqrt d * ‖p⁻¹ * q‖) ^ (d - 1) *
              (3 : ℝ) ^ (c - n)) *
        volume (adaptedCellAt p n w) := by
  classical
  set t : ℝ := ‖p⁻¹ * q‖ * (Real.sqrt d * (3 : ℝ) ^ c) with htdef
  have ht : 0 ≤ t := by positivity
  have hdet : IsUnit p.det := (Matrix.isUnit_iff_isUnit_det p).mp hp.isUnit
  have hinv : ∀ z : Vec d, matVecMul p (matVecMul p⁻¹ z) = z := by
    intro z
    show p *ᵥ p⁻¹ *ᵥ z = z
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hsub : {x : Vec d | x ∉ adaptedCellAt p n w ∧
      ∃ v : Fin d → ℤ, x ∈ adaptedCellAt q c v ∧
        (adaptedCellAt q c v ∩ adaptedCellAt p n w).Nonempty} ⊆
      (fun z => adaptedCellCenter p n w + matVecMul p z) ''
        {z : Vec d |
          (∀ k, |z k| < (1 / 2 : ℝ) * (3 : ℝ) ^ n + t) ∧
            ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ |z i|} := by
    rintro x ⟨hxout, v, hxv, z, hzv, hzp⟩
    obtain ⟨xq, hxq, hxqeq⟩ := (Recurrence.adaptedCellAt_eq_image q c v ▸ hxv)
    obtain ⟨zq, hzq, hzqeq⟩ := (Recurrence.adaptedCellAt_eq_image q c v ▸ hzv)
    obtain ⟨zp, hzp0, hzpeq⟩ := (Recurrence.adaptedCellAt_eq_image p n w ▸ hzp)
    obtain ⟨zc, hzc, hzceq⟩ := (Recurrence.standardCell_eq_image n w ▸ hzp0)
    set xt : Vec d := matVecMul p⁻¹ (x - adaptedCellCenter p n w) with hxtdef
    have hxrepr : adaptedCellCenter p n w + matVecMul p xt = x := by
      rw [hxtdef, hinv]
      abel
    have hdiff : xt - zc = matVecMul (p⁻¹ * q) (xq - zq) := by
      have hzcenter : adaptedCellCenter p n w + matVecMul p zc = z := by
        change standardCellCenter n w + zc = zp at hzceq
        rw [Recurrence.adaptedCellCenter_eq, ← matVecMul_add, hzceq]
        exact hzpeq
      have hp1 : matVecMul p (xt - zc) = matVecMul q (xq - zq) := by
        rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg,
          eq_sub_of_add_eq' hxrepr, eq_sub_of_add_eq' hzcenter,
          sub_eq_add_neg (a := xq), matVecMul_add, matVecMul_neg, hxqeq, hzqeq]
        abel
      have hp2 : matVecMul p⁻¹ (matVecMul p (xt - zc)) = xt - zc := by
        show p⁻¹ *ᵥ p *ᵥ (xt - zc) = xt - zc
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
      rw [← hp2, hp1, matVecMul_mul]
    have hcell : ∀ k, |(xq - zq) k| ≤ (3 : ℝ) ^ c := by
      intro k
      rw [Recurrence.mem_standardCell_iff] at hxq hzq
      have h1 := hxq k
      have h2 := hzq k
      rw [Pi.sub_apply, abs_le]
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
    have hclose : ∀ i, |xt i - zc i| ≤ t := by
      intro i
      have h := abs_matVecMul_le_of_abs_le (p⁻¹ * q) hcell i
      rw [← hdiff] at h
      change |xt i - zc i| ≤ ‖p⁻¹ * q‖ * (Real.sqrt d * (3 : ℝ) ^ c) at h
      rw [htdef]
      exact h
    have hzin : ∀ i, |zc i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
      intro i
      rw [Recurrence.mem_centeredCube_iff] at hzc
      rw [abs_lt]
      exact ⟨by linarith only [(hzc i).1], by linarith only [(hzc i).2]⟩
    have hxtout : xt ∉ centeredCube d n := by
      intro hmem
      apply hxout
      rw [Recurrence.adaptedCellAt_eq_image, Recurrence.standardCell_eq_image]
      refine ⟨standardCellCenter n w + xt, ⟨xt, hmem, rfl⟩, ?_⟩
      rw [matVecMul_add, ← Recurrence.adaptedCellCenter_eq]
      exact hxrepr
    obtain ⟨i, hi⟩ : ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ |xt i| := by
      by_contra hcon
      push Not at hcon
      refine hxtout (Recurrence.mem_centeredCube_iff.mpr fun i => ?_)
      have hi := hcon i
      rw [abs_lt] at hi
      exact ⟨by linarith only [hi.1], hi.2⟩
    refine ⟨xt, ⟨fun i => ?_, i, hi⟩, hxrepr⟩
    calc
      |xt i| = |(xt i - zc i) + zc i| := by ring_nf
      _ ≤ |xt i - zc i| + |zc i| := abs_add_le _ _
      _ ≤ t + |zc i| := by
        simpa [add_comm] using add_le_add_right (hclose i) |zc i|
      _ < (1 / 2 : ℝ) * (3 : ℝ) ^ n + t := by linarith only [hzin i]
  refine (measure_mono hsub).trans ?_
  rw [volume_image_affine]
  refine (mul_le_mul' le_rfl (volume_outer_layer_centeredCube_le n ht)).trans ?_
  rw [adaptedCellAt_eq_adaptedCellTranslate, volume_adaptedCellTranslate]
  have hbase : (3 : ℝ) ^ n + 2 * t ≤
      (3 : ℝ) ^ n * (1 + 6 * Real.sqrt d * ‖p⁻¹ * q‖) := by
    have hmul : (3 : ℝ) ^ c ≤ (3 : ℝ) ^ n :=
      zpow_le_zpow_right₀ (by norm_num) hcn
    have hfac : (0 : ℝ) ≤ Real.sqrt d * ‖p⁻¹ * q‖ := by positivity
    have hscaled : 2 * (Real.sqrt d * ‖p⁻¹ * q‖) * (3 : ℝ) ^ c ≤
        6 * (Real.sqrt d * ‖p⁻¹ * q‖) * (3 : ℝ) ^ n := by
      calc
        2 * (Real.sqrt d * ‖p⁻¹ * q‖) * (3 : ℝ) ^ c ≤
            2 * (Real.sqrt d * ‖p⁻¹ * q‖) * (3 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
        _ ≤ 6 * (Real.sqrt d * ‖p⁻¹ * q‖) * (3 : ℝ) ^ n := by
          have h3n : (0 : ℝ) ≤ (3 : ℝ) ^ n := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith only [hfac]) h3n
    rw [htdef]
    calc
      (3 : ℝ) ^ n + 2 * (‖p⁻¹ * q‖ * (Real.sqrt d * (3 : ℝ) ^ c)) ≤
          (3 : ℝ) ^ n + 6 * (Real.sqrt d * ‖p⁻¹ * q‖) * (3 : ℝ) ^ n := by
        linarith only [hscaled]
      _ = (3 : ℝ) ^ n * (1 + 6 * Real.sqrt d * ‖p⁻¹ * q‖) := by ring
  have hpow := pow_le_pow_left₀ (by positivity) hbase (d - 1)
  have hcoeff : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
      (1 + 6 * Real.sqrt d * ‖p⁻¹ * q‖) ^ (d - 1) *
        (3 : ℝ) ^ (c - n) := by positivity
  rw [← ENNReal.ofReal_mul (abs_nonneg p.det),
    ← ENNReal.ofReal_mul hcoeff]
  refine ENNReal.ofReal_le_ofReal ?_
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hpowid : (3 : ℝ) ^ (n * (d : ℤ)) = ((3 : ℝ) ^ n) ^ d := by
    rw [← zpow_natCast ((3 : ℝ) ^ n) d, ← zpow_mul]
  rw [hpowid]
  calc
    |p.det| * (2 * (d : ℝ) * t * ((3 : ℝ) ^ n + 2 * t) ^ (d - 1))
        ≤ |p.det| * (2 * (d : ℝ) * t *
            (((3 : ℝ) ^ n * (1 + 6 * Real.sqrt d * ‖p⁻¹ * q‖)) ^ (d - 1))) := by
          gcongr
    _ = (2 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
          (1 + 6 * Real.sqrt d * ‖p⁻¹ * q‖) ^ (d - 1) *
            (3 : ℝ) ^ (c - n)) *
          (|p.det| * ((3 : ℝ) ^ n) ^ d) := by
        rw [htdef, mul_pow, zpow_sub₀ h3]
        have hdpos : 0 < d := NeZero.ne d |> Nat.pos_of_ne_zero
        have hdpow : ((3 : ℝ) ^ n) ^ d =
            ((3 : ℝ) ^ n) ^ (d - 1) * (3 : ℝ) ^ n := by
          calc
            ((3 : ℝ) ^ n) ^ d = ((3 : ℝ) ^ n) ^ ((d - 1) + 1) := by
              congr 1
              omega
            _ = ((3 : ℝ) ^ n) ^ (d - 1) * (3 : ℝ) ^ n := by
              rw [pow_add, pow_one]
        rw [hdpow]
        field_simp

end

end Transport
end HighContrast
end Homogenization
