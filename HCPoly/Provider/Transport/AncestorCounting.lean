/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WhitneyRows

/-!
# The number of ancestors of a target cell

The last sentence of the inherited-rows paragraph of the grid transport: for a
scale-`n` cell of the new grid there are at most `C(d,K_hop)3^{d(n-b)}` aligned
scale-`b` cells of the old grid that meet it.  This is the factor the terminal
weight has to absorb once the inherited contribution has been grouped by
ancestors, and it is the counterpart, on the *old* grid, of the target
multiplicity `3^{d(n-j)}` of the aligned subdivision — with the cross-grid
constant `K_hop` in place of the exact count, because the two grids are only
comparable, not nested.

The proof is the index computation the aligned subdivision already runs, carried
across the grids.  A point of the target, read in the coordinates of the old
grid, lies within `‖q^{-1}p‖√d 3^n/2` of the fixed vector `q^{-1}y`; a point of
an aligned scale-`b` cell has index within `1/2` of `3^{-b}` times its own
coordinate vector.  So every index of a cell meeting the target lies, coordinate
by coordinate, in an interval of length `1 + ‖q^{-1}p‖√d 3^{n-b}` around a single
point, and the count is the product over the `d` coordinates of the number of
integers in that interval.  The grid ratio dominates `‖q^{-1}p‖`, and `3^{n-b}`
is at least one, so the constant `(2 + √d K_hop)^d` is exhibited and the printed
shape `C(d,K_hop)3^{d(n-b)}` is reached.

No containment is asserted and none is needed: unlike the target cells of the
new grid, the ancestors are not required to sit inside anything, which is
exactly why the count is by comparability rather than by exact subdivision.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The index of a cell meeting the target -/

/-- **A cell meeting the target has a controlled index.**  If the aligned
scale-`b` cell of the grid `q` at the index `w` meets the translated scale-`n`
cell `y + ⋄_n^p` of the grid `p`, then every coordinate of `w` lies within
`1/2 + √d‖q^{-1}p‖3^{n-b}/2` of the corresponding coordinate of the fixed vector
`3^{-b}q^{-1}y`, which does not depend on `w`.

Both halves are coordinate estimates: the cell pins its own index to within
`1/2` after rescaling, and the target has `q`-coordinate diameter at most
`‖q^{-1}p‖√d3^n`. -/
theorem abs_index_sub_le_of_meets {p q : Mat d} (hq : q.PosDef) {b n : ℤ} {y : Vec d}
    {w : Fin d → ℤ}
    (hmeet : (adaptedCellAt q b w ∩ adaptedCellTranslate p n y).Nonempty) (i : Fin d) :
    |(w i : ℝ) - (3 : ℝ) ^ (-b) * matVecMul q⁻¹ y i| ≤
      1 / 2 + Real.sqrt d * ‖q⁻¹ * p‖ * (3 : ℝ) ^ (n - b) / 2 := by
  obtain ⟨x, hxq, hxp⟩ := hmeet
  rw [Recurrence.adaptedCellAt_eq_image] at hxq
  obtain ⟨u, hu, hux⟩ := hxq
  rw [adaptedCellTranslate_eq_image] at hxp
  obtain ⟨z, hz, hzx⟩ := hxp
  have hzx' : y + matVecMul p z = x := hzx
  have h3 : (0 : ℝ) ≠ 3 := by norm_num
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hinv : matVecMul q⁻¹ (matVecMul q u) = u := by
    show q⁻¹ *ᵥ q *ᵥ u = u
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hueq : u = matVecMul q⁻¹ y + matVecMul (q⁻¹ * p) z := by
    have h1 : matVecMul q⁻¹ (matVecMul q u) = matVecMul q⁻¹ (y + matVecMul p z) := by
      rw [hux, hzx']
    rwa [hinv, matVecMul_add, matVecMul_mul] at h1
  have hui : u i = matVecMul q⁻¹ y i + matVecMul (q⁻¹ * p) z i := congrFun hueq i
  have hzb : ∀ k, |z k| ≤ (3 : ℝ) ^ n / 2 := by
    intro k
    rw [Recurrence.mem_centeredCube_iff] at hz
    obtain ⟨h1, h2⟩ := hz k
    rw [abs_le]
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  have hcoord : |matVecMul (q⁻¹ * p) z i| ≤ ‖q⁻¹ * p‖ * (Real.sqrt d * ((3 : ℝ) ^ n / 2)) :=
    abs_matVecMul_le_of_abs_le (q⁻¹ * p) hzb i
  rw [abs_le] at hcoord
  rw [Recurrence.mem_standardCell_iff] at hu
  obtain ⟨hu1, hu2⟩ := hu i
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-b) := by positivity
  have hpow : (3 : ℝ) ^ (-b) * (3 : ℝ) ^ b = 1 := by
    rw [← zpow_add₀ h3.symm]
    simp
  have hsub : (3 : ℝ) ^ (-b) * (3 : ℝ) ^ n = (3 : ℝ) ^ (n - b) := by
    rw [← zpow_add₀ h3.symm]
    congr 1
    ring
  have hlow : (w i : ℝ) - 1 / 2 < (3 : ℝ) ^ (-b) * u i := by
    have hmul := mul_lt_mul_of_pos_left hu1 ht
    have he : (3 : ℝ) ^ (-b) * (((w i : ℝ) - 1 / 2) * (3 : ℝ) ^ b) =
        ((w i : ℝ) - 1 / 2) * ((3 : ℝ) ^ (-b) * (3 : ℝ) ^ b) := by ring
    rw [he, hpow, mul_one] at hmul
    exact hmul
  have hhigh : (3 : ℝ) ^ (-b) * u i < (w i : ℝ) + 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_left hu2 ht
    have he : (3 : ℝ) ^ (-b) * (((w i : ℝ) + 1 / 2) * (3 : ℝ) ^ b) =
        ((w i : ℝ) + 1 / 2) * ((3 : ℝ) ^ (-b) * (3 : ℝ) ^ b) := by ring
    rw [he, hpow, mul_one] at hmul
    exact hmul
  have hscaled : (3 : ℝ) ^ (-b) * u i =
      (3 : ℝ) ^ (-b) * matVecMul q⁻¹ y i + (3 : ℝ) ^ (-b) * matVecMul (q⁻¹ * p) z i := by
    rw [hui]
    ring
  have hup : (3 : ℝ) ^ (-b) * matVecMul (q⁻¹ * p) z i ≤
      Real.sqrt d * ‖q⁻¹ * p‖ * (3 : ℝ) ^ (n - b) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcoord.2 ht.le
    have he : (3 : ℝ) ^ (-b) * (‖q⁻¹ * p‖ * (Real.sqrt d * ((3 : ℝ) ^ n / 2))) =
        Real.sqrt d * ‖q⁻¹ * p‖ * ((3 : ℝ) ^ (-b) * (3 : ℝ) ^ n) / 2 := by ring
    rw [he, hsub] at hmul
    exact hmul
  have hdn : -(Real.sqrt d * ‖q⁻¹ * p‖ * (3 : ℝ) ^ (n - b) / 2) ≤
      (3 : ℝ) ^ (-b) * matVecMul (q⁻¹ * p) z i := by
    have hmul := mul_le_mul_of_nonneg_left hcoord.1 ht.le
    have he : (3 : ℝ) ^ (-b) * -(‖q⁻¹ * p‖ * (Real.sqrt d * ((3 : ℝ) ^ n / 2))) =
        -(Real.sqrt d * ‖q⁻¹ * p‖ * ((3 : ℝ) ^ (-b) * (3 : ℝ) ^ n) / 2) := by ring
    rw [he, hsub] at hmul
    exact hmul
  rw [abs_le]
  constructor
  · linarith only [hhigh, hscaled, hdn]
  · linarith only [hlow, hscaled, hup]

/-! ## Counting the integers of one coordinate -/

/-- The integers of a bounded interval, counted through the floor and the
ceiling: the cardinality of `Icc ⌈v⌉ ⌊u⌋` is at most `u - v + 1`. -/
private theorem card_Icc_ceil_floor_le {u v : ℝ} (h : 0 ≤ u - v + 1) :
    (((⌊u⌋ + 1 - ⌈v⌉).toNat : ℕ) : ℝ) ≤ u - v + 1 := by
  rcases le_or_gt (⌊u⌋ + 1 - ⌈v⌉) 0 with hm | hm
  · rw [Int.toNat_eq_zero.mpr hm]
    simpa using h
  · have hcast : (((⌊u⌋ + 1 - ⌈v⌉).toNat : ℕ) : ℝ) = (⌊u⌋ : ℝ) + 1 - (⌈v⌉ : ℝ) := by
      have hz : (((⌊u⌋ + 1 - ⌈v⌉).toNat : ℕ) : ℤ) = ⌊u⌋ + 1 - ⌈v⌉ :=
        Int.toNat_of_nonneg hm.le
      exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) hz
    rw [hcast]
    have h1 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
    have h2 : v ≤ (⌈v⌉ : ℝ) := Int.le_ceil v
    linarith only [h1, h2]

/-! ## The ancestor count -/

/-- The relevant ancestors are confined to a product of coordinate intervals,
whose integer points are counted by the exhibited constant. -/
private theorem exists_ancestor_finset {p q : Mat d} (hd : 1 ≤ d) (hq : q.PosDef) {b n : ℤ}
    (hbn : b ≤ n) {y : Vec d} {Khop : ℝ} (hK : gridRatio q p ≤ Khop) :
    ∃ Y : Finset (Fin d → ℤ),
      {w : Fin d → ℤ | (adaptedCellAt q b w ∩ adaptedCellTranslate p n y).Nonempty} ⊆ ↑Y ∧
        (Y.card : ℝ) ≤ (2 + Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((n - b) * (d : ℤ)) := by
  classical
  have hnorm : ‖q⁻¹ * p‖ ≤ Khop := le_trans (norm_inv_mul_le_gridRatio hd q p).2 hK
  have hK0 : (0 : ℝ) ≤ Khop := le_trans (norm_nonneg _) hnorm
  have hsq : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hgap : (1 : ℝ) ≤ (3 : ℝ) ^ (n - b) := by
    refine one_le_zpow₀ (by norm_num) ?_
    omega
  have hgap0 : (0 : ℝ) < (3 : ℝ) ^ (n - b) := by positivity
  set c : Fin d → ℝ := fun i => (3 : ℝ) ^ (-b) * matVecMul q⁻¹ y i with hc
  set rho : ℝ := 1 / 2 + Real.sqrt d * Khop * (3 : ℝ) ^ (n - b) / 2 with hrho
  have hrho0 : (0 : ℝ) ≤ rho := by
    have : (0 : ℝ) ≤ Real.sqrt d * Khop * (3 : ℝ) ^ (n - b) :=
      mul_nonneg (mul_nonneg hsq hK0) hgap0.le
    rw [hrho]
    linarith only [this]
  refine ⟨Fintype.piFinset fun i => Finset.Icc ⌈c i - rho⌉ ⌊c i + rho⌋, ?_, ?_⟩
  · -- every index of the family lies in the product of intervals
    intro w hw
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    have hbound := abs_index_sub_le_of_meets hq hw i
    have hmono : Real.sqrt d * ‖q⁻¹ * p‖ * (3 : ℝ) ^ (n - b) / 2 ≤
        Real.sqrt d * Khop * (3 : ℝ) ^ (n - b) / 2 := by
      have hstep : Real.sqrt d * ‖q⁻¹ * p‖ ≤ Real.sqrt d * Khop :=
        mul_le_mul_of_nonneg_left hnorm hsq
      have := mul_le_mul_of_nonneg_right hstep hgap0.le
      linarith only [this]
    rw [abs_le] at hbound
    rw [Finset.mem_Icc, hc, hrho]
    constructor
    · exact Int.ceil_le.mpr (by linarith only [hbound.1, hmono])
    · exact Int.le_floor.mpr (by linarith only [hbound.2, hmono])
  have hcard : (((Fintype.piFinset fun i => Finset.Icc ⌈c i - rho⌉ ⌊c i + rho⌋).card : ℕ) : ℝ) ≤
      (2 * rho + 1) ^ d := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
    have hfac : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        (((Finset.Icc ⌈c i - rho⌉ ⌊c i + rho⌋).card : ℕ) : ℝ) ≤ 2 * rho + 1 := by
      intro i _
      rw [Int.card_Icc]
      have hval : c i + rho - (c i - rho) + 1 = 2 * rho + 1 := by ring
      have := card_Icc_ceil_floor_le (u := c i + rho) (v := c i - rho)
        (by rw [hval]; linarith only [hrho0])
      rw [hval] at this
      exact this
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        (0 : ℝ) ≤ (((Finset.Icc ⌈c i - rho⌉ ⌊c i + rho⌋).card : ℕ) : ℝ) :=
      fun i _ => Nat.cast_nonneg _
    refine le_trans (Finset.prod_le_prod hnn hfac) ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine le_trans hcard ?_
  have hbase : 2 * rho + 1 ≤ (2 + Real.sqrt d * Khop) * (3 : ℝ) ^ (n - b) := by
    have h2 : (2 : ℝ) ≤ 2 * (3 : ℝ) ^ (n - b) := by linarith only [hgap]
    rw [hrho]
    nlinarith only [h2, hgap0, hsq, hK0]
  have hpow : (2 * rho + 1) ^ d ≤ ((2 + Real.sqrt d * Khop) * (3 : ℝ) ^ (n - b)) ^ d :=
    pow_le_pow_left₀ (by linarith only [hrho0]) hbase d
  refine le_trans hpow (le_of_eq ?_)
  rw [mul_pow, ← zpow_natCast ((3 : ℝ) ^ (n - b)) d, ← zpow_mul]

/-- **The relevant ancestors are finitely many.**  The aligned scale-`b` cells of
the old grid meeting a translated scale-`n` cell of the new grid form a finite
family, so the grouping of the inherited sources by ancestors is a finite
sum. -/
theorem finite_ancestors {p q : Mat d} (hd : 1 ≤ d) (hq : q.PosDef) {b n : ℤ}
    (hbn : b ≤ n) {y : Vec d} :
    {w : Fin d → ℤ |
      (adaptedCellAt q b w ∩ adaptedCellTranslate p n y).Nonempty}.Finite := by
  obtain ⟨Y, hsub, -⟩ :=
    exists_ancestor_finset hd hq hbn (y := y) (Khop := gridRatio q p) le_rfl
  exact Y.finite_toSet.subset hsub

/-- **The same count for a family given as a finite set of indices**, the form
the grouping step produces: nothing is assumed about how the family was made,
only that each of its cells meets the target, so the bound applies directly to
the ancestors of the selected sources of the filling. -/
theorem card_ancestors_le {p q : Mat d} (hd : 1 ≤ d) (hq : q.PosDef) {b n : ℤ}
    (hbn : b ≤ n) {y : Vec d} {Khop : ℝ} (hK : gridRatio q p ≤ Khop)
    {Z : Finset (Fin d → ℤ)}
    (hZ : ∀ w ∈ Z, (adaptedCellAt q b w ∩ adaptedCellTranslate p n y).Nonempty) :
    (Z.card : ℝ) ≤
      (2 + Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((n - b) * (d : ℤ)) := by
  obtain ⟨Y, hsub, hY⟩ := exists_ancestor_finset hd hq hbn (y := y) hK
  refine le_trans ?_ hY
  have hle : Z.card ≤ Y.card :=
    Finset.card_le_card fun w hw => Finset.mem_coe.mp (hsub (hZ w hw))
  exact_mod_cast hle

/-- **The ancestor count in the extended nonnegative reals**, the form the
max-to-sum step of the inherited rows consumes: the cardinality of a family of
scale-`b` ancestors of a scale-`n` target, read in `ℝ≥0∞`, is at most the
printed count. -/
theorem card_ancestors_le_ofReal {p q : Mat d} (hd : 1 ≤ d) (hq : q.PosDef) {b n : ℤ}
    (hbn : b ≤ n) {y : Vec d} {Khop : ℝ} (hK : gridRatio q p ≤ Khop)
    {Z : Finset (Fin d → ℤ)}
    (hZ : ∀ w ∈ Z, (adaptedCellAt q b w ∩ adaptedCellTranslate p n y).Nonempty) :
    (Z.card : ENNReal) ≤
      ENNReal.ofReal ((2 + Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((n - b) * (d : ℤ))) := by
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (card_ancestors_le hd hq hbn hK hZ)

/-! ## The relevant ancestors of the filling -/

/-- **An ancestor of a cell of the filling meets the target.**  This is the only
link the grouping step needs: a selected source lies in the target and in its own
scale-`b` ancestor, and it is nonempty, so the ancestor is one of the cells the
count applies to. -/
theorem ancestor_meets_of_subset {q : Mat d} {a b : ℤ} {w v : Fin d → ℤ}
    {W : Set (Vec d)} (hVB : adaptedCellAt q a v ⊆ adaptedCellAt q b w)
    (hVW : adaptedCellAt q a v ⊆ W) : (adaptedCellAt q b w ∩ W).Nonempty := by
  obtain ⟨x, hx⟩ := Recurrence.adaptedCellAt_nonempty q a v
  exact ⟨x, hVB hx, hVW hx⟩

end

end Transport
end HighContrast
end Homogenization
