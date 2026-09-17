import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm
import HCPoly.Entry.Multiscale.ResponseInputs.HC2a_ReferenceCubePullback

/-!
# Grouping the triadic index box at `3 ^ n`

`triadicIndexBox d m` indexes the `3 ^ (m * d)` aligned cells of generation `t - m` inside the
adapted cell of generation `t`.  Writing a generation gap as `H + n`, every depth-`(H + n)` index
`W` splits uniquely as `W = 3 ^ n * w + z`, with `w` the outer index of the depth-`H` cell
containing the cell and `z` the inner index of the cell inside it.  This is balanced ternary with
the digits grouped at `3 ^ n`.  It is what lets the descendant sum of `p.response.transfer` read
the annealed head of the source load: the `3 ^ ((H + n) * d)` descendants of the terminal cell at
generation `s - n` are exactly `3 ^ (H * d)` translated copies of the `3 ^ (n * d)` descendants of
one scale-`s` cell.

The proof needs no explicit inverse: the grouped-digit map is injective and the two finsets have
the same cardinality, so its image is everything.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- `triadicIndexBound m = (3 ^ m - 1) / 2` is the radius of the depth-`m` index box
`triadicIndexBox d m`, i.e. the box is the integer interval `[-b m, b m]` in every coordinate. -/
private def triadicIndexBound (m : ℕ) : ℕ := (3 ^ m - 1) / 2

/-- Twice the radius of the depth-`m` index box is `3 ^ m - 1`, since `3 ^ m` is odd. -/
private theorem two_mul_triadicIndexBound (m : ℕ) :
    2 * (triadicIndexBound m : ℤ) = (3 : ℤ) ^ m - 1 := by
  obtain ⟨k, hk⟩ : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
  have hb : triadicIndexBound m = k := by
    unfold triadicIndexBound
    omega
  have hkz : (3 : ℤ) ^ m = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  rw [hb, hkz]
  ring

/-- The radius of the depth-`(H + n)` box is the grouped-digit bound `3 ^ n * b H + b n`. -/
private theorem triadicIndexBound_add (H n : ℕ) :
    (triadicIndexBound (H + n) : ℤ)
      = 3 ^ n * (triadicIndexBound H : ℤ) + (triadicIndexBound n : ℤ) := by
  obtain ⟨kH, hkH⟩ : Odd ((3 : ℕ) ^ H) := Odd.pow (by decide)
  obtain ⟨kn, hkn⟩ : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
  have hbH : triadicIndexBound H = kH := by
    unfold triadicIndexBound
    omega
  have hbn : triadicIndexBound n = kn := by
    unfold triadicIndexBound
    omega
  have hmain : triadicIndexBound (H + n) = 3 ^ n * kH + kn := by
    unfold triadicIndexBound
    have hpow : 3 ^ (H + n) = 2 * (3 ^ n * kH + kn) + 1 := by
      rw [pow_add, hkH, hkn]
      ring
    omega
  rw [hbH, hbn, hmain]
  push_cast
  ring

/-- **The grouped-digit index is in the box.**  If the outer index `w` lies in the box of depth
`H` and the inner index `z` in the box of depth `n`, then `3^n w + z` lies in the box of depth
`H + n`. -/
theorem mem_triadicIndexBox_add_of_mem {d H n : ℕ} {w z : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d H) (hz : z ∈ triadicIndexBox d n) :
    (fun i => 3 ^ n * w i + z i) ∈ triadicIndexBox d (H + n) := by
  rw [mem_triadicIndexBox_iff]
  intro i
  have hwi : |w i| ≤ (triadicIndexBound H : ℤ) := by
    simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hw) i
  have hzi : |z i| ≤ (triadicIndexBound n : ℤ) := by
    simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hz) i
  have hwnn : (0 : ℤ) ≤ (3 : ℤ) ^ n := pow_nonneg (by norm_num) n
  calc
    |(3 : ℤ) ^ n * w i + z i| ≤ |(3 : ℤ) ^ n * w i| + |z i| := abs_add_le ..
    _ = (3 : ℤ) ^ n * |w i| + |z i| := by rw [abs_mul, abs_of_nonneg hwnn]
    _ ≤ (3 : ℤ) ^ n * (triadicIndexBound H : ℤ) + (triadicIndexBound n : ℤ) :=
          add_le_add (mul_le_mul_of_nonneg_left hwi hwnn) hzi
    _ = (((3 ^ (H + n) - 1) / 2 : ℕ) : ℤ) := by
          rw [← triadicIndexBound_add H n]
          simp only [triadicIndexBound]

/-- **The grouped-digit map is injective.**  Two pairs of an outer and an inner index that give
the same grouped index are equal: the inner digits span less than one outer step. -/
theorem triadicIndexBox_add_injOn {d H n : ℕ} {w z w' z' : Fin d → ℤ}
    (hz : z ∈ triadicIndexBox d n) (hz' : z' ∈ triadicIndexBox d n)
    (h : (fun i => 3 ^ n * w i + z i) = (fun i => 3 ^ n * w' i + z' i)) :
    w = w' ∧ z = z' := by
  have hnpos : (0 : ℤ) < (3 : ℤ) ^ n := pow_pos (by norm_num) n
  have main : w = w' ∧ z = z' := by
    have hw : w = w' := by
      funext i
      have hzi : |z i| ≤ (triadicIndexBound n : ℤ) := by
        simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hz) i
      have hz'i : |z' i| ≤ (triadicIndexBound n : ℤ) := by
        simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hz') i
      have hdiff_le : |z' i - z i| ≤ 2 * (triadicIndexBound n : ℤ) := by
        obtain ⟨h1, h2⟩ := abs_le.mp hzi
        obtain ⟨h1', h2'⟩ := abs_le.mp hz'i
        rw [abs_le]
        constructor <;> omega
      have hdiff_lt : |z' i - z i| < (3 : ℤ) ^ n := by
        have h2b := two_mul_triadicIndexBound n
        rw [h2b] at hdiff_le
        omega
      have hmul : (3 : ℤ) ^ n * (w i - w' i) = z' i - z i := by
        have hi : (3 : ℤ) ^ n * w i + z i = (3 : ℤ) ^ n * w' i + z' i := by
          simpa only [] using congrFun h i
        have hsub : (3 : ℤ) ^ n * w i - (3 : ℤ) ^ n * w' i = z' i - z i := by
          linarith
        simpa only [mul_sub] using hsub
      have habs : (3 : ℤ) ^ n * |w i - w' i| = |z' i - z i| := by
        rw [← hmul, abs_mul, abs_of_nonneg (le_of_lt hnpos)]
      by_contra hne
      have hge1 : 1 ≤ |w i - w' i| := Int.one_le_abs (sub_ne_zero.mpr hne)
      have hle : (3 : ℤ) ^ n ≤ (3 : ℤ) ^ n * |w i - w' i| := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hge1 (le_of_lt hnpos)
      rw [habs] at hle
      exact (not_le.mpr hdiff_lt) hle
    refine ⟨hw, ?_⟩
    funext i
    have hi : (3 : ℤ) ^ n * w i + z i = (3 : ℤ) ^ n * w' i + z' i := by
      simpa only [] using congrFun h i
    rw [congrFun hw i] at hi
    exact add_left_cancel hi
  have aux : ∀ _k : ℕ, w = w' ∧ z = z' := fun _ => main
  exact aux H

/-- The grouped-digit map `(w, z) ↦ (fun i => 3 ^ n * w i + z i)` on pairs of indices. -/
private abbrev groupedIndex {d : ℕ} (n : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) : Fin d → ℤ :=
  fun i => 3 ^ n * p.1 i + p.2 i

/-- **The index box of depth `H + n` is the grouped product of the boxes of depths `H` and
`n`.**  Summing a function over the depth-`(H+n)` box is summing it over the outer box of the
depth-`H` cells and, inside each, over the inner box of the depth-`n` descendants. -/
theorem sum_triadicIndexBox_add {d : ℕ} [NeZero d] (H n : ℕ) (F : (Fin d → ℤ) → ℝ) :
    ∑ W ∈ triadicIndexBox d (H + n), F W
      = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
          F (fun i => 3 ^ n * w i + z i) := by
  classical
  have hmem : ∀ p ∈ (triadicIndexBox d H) ×ˢ (triadicIndexBox d n),
      groupedIndex n p ∈ triadicIndexBox d (H + n) := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact mem_triadicIndexBox_add_of_mem hp.1 hp.2
  have hinj : Set.InjOn (groupedIndex n)
      (((triadicIndexBox d H) ×ˢ (triadicIndexBox d n) :
        Finset ((Fin d → ℤ) × (Fin d → ℤ))) : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    intro p hp q hq heq
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    have heq' : (fun i => 3 ^ n * p.1 i + p.2 i) = (fun i => 3 ^ n * q.1 i + q.2 i) := heq
    obtain ⟨hw', hz'⟩ := triadicIndexBox_add_injOn (H := H) hp.2 hq.2 heq'
    exact Prod.ext hw' hz'
  have hcard : ((triadicIndexBox d H) ×ˢ (triadicIndexBox d n)).card
      = (triadicIndexBox d (H + n)).card := by
    rw [Finset.card_product, card_triadicIndexBox_nat H, card_triadicIndexBox_nat n,
      card_triadicIndexBox_nat (H + n), ← mul_pow, ← pow_add]
  have himage : ((triadicIndexBox d H) ×ˢ (triadicIndexBox d n)).image (groupedIndex n)
      = triadicIndexBox d (H + n) := by
    refine Finset.eq_of_subset_of_card_le (fun W hW => ?_) ?_
    · rw [Finset.mem_image] at hW
      obtain ⟨p, hp, rfl⟩ := hW
      exact hmem p hp
    · rw [Finset.card_image_of_injOn hinj]
      exact hcard.ge
  calc
    ∑ W ∈ triadicIndexBox d (H + n), F W
        = ∑ W ∈ ((triadicIndexBox d H) ×ˢ (triadicIndexBox d n)).image (groupedIndex n),
            F W := by rw [himage]
    _ = ∑ p ∈ (triadicIndexBox d H) ×ˢ (triadicIndexBox d n), F (groupedIndex n p) := by
          rw [Finset.sum_image hinj]
    _ = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            F (groupedIndex n (w, z)) := by
          rw [Finset.sum_product]
    _ = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            F (fun i => 3 ^ n * w i + z i) := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rfl

end

end Homogenization.HighContrast.Multiscale
