import HCPoly.Entry.Geometry.WhitneyExhaustion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HCPoly.Setup.Geometry

/-!
# Standard cubes inside an adapted cube

`l.source.whitney`.  For `W = y + ⋄_j^q`, the
maximal standard aligned cubes contained in `W` with generation at most `j` partition `W`
up to a null set (`WhitneyExhaustion.lean` and `MaximalCells.lean`), and for `r ≤ j` those of
generation `r` satisfy
`Σ_{z ∈ 𝒵_r(W)} |□_r| / |W| ≤ 12 d^{3/2} 3^{r-j}`.
This file proves the volume bound and states the lemma as one package, `source_whitney`.

The manuscript sets `q = 𝒬(m)` and uses only `|q⁻¹| ≤ 2` from `e.rounded.grid.bounds`
(near `e.rounded.grid.bounds`).  Here that bound is the hypothesis `InverseNormLE q 2`; the constant
`12 d^{3/2} = 4d · √d · 3` is produced by the proof, uniformly in `q`.
-/

open Homogenization.HighContrast (adaptedCellTranslate standardCell)
namespace Homogenization.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

/-! ## The row of generation `r` against the target -/

/-- A row of maximal cubes never exceeds the target: its members are disjoint subsets
of `W`. -/
theorem volume_biUnion_maximalCellIndices_le_target (W : Set (Vec d)) (j r : ℤ) :
    volume (⋃ w ∈ maximalCellIndices W j r, standardCell d r w) ≤ volume W := by
  refine measure_mono ?_
  intro x hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  exact hw.subset hxw

/-- Every point of a maximal cube of generation `r < j` is within Euclidean distance
`√d 3^{r+1}` of a point outside `W`: the parent escapes `W`. -/
theorem exists_not_mem_of_mem_maximalCell [NeZero d] {W : Set (Vec d)} {j r : ℤ} (hrj : r < j)
    {w : Fin d → ℤ} (hw : w ∈ maximalCellIndices W j r) {x : Vec d}
    (hx : x ∈ standardCell d r w) :
    ∃ x', x' ∉ W ∧ ∑ i, (x i - x' i) ^ 2 ≤ (Real.sqrt d * (3 : ℝ) ^ (r + 1)) ^ 2 := by
  have hpar := hw.parent_not_subset hrj
  obtain ⟨x', hx'par, hx'W⟩ := Set.not_subset.mp hpar
  refine ⟨x', hx'W, ?_⟩
  have hxpar := standardCell_subset_parent r w hx
  refine (sum_sq_sub_le_of_mem_standardCell hxpar hx'par).trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

/-- **The row bound in measure form.**  For `r < j` and `|q⁻¹| ≤ K`, the maximal cubes of
generation `r` have total volume at most `2d · K √d 3^{r+1} · 3^{-j}` times `|W|`. -/
theorem volume_biUnion_maximalCellIndices_le [NeZero d] {q : Mat d} {K : ℝ} (hK : 0 ≤ K)
    (hq : InverseNormLE q K) {j r : ℤ} (hrj : r < j) (y : Vec d) :
    volume (⋃ w ∈ maximalCellIndices (adaptedCellTranslate q j y) j r, standardCell d r w) ≤
      ENNReal.ofReal (2 * (d : ℝ) * (K * (Real.sqrt d * (3 : ℝ) ^ (r + 1))) * (3 : ℝ) ^ (-j)) *
        volume (adaptedCellTranslate q j y) := by
  refine volume_le_of_near_complement hK hq (by positivity) ?_ ?_
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact hw.subset hxw
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact exists_not_mem_of_mem_maximalCell hrj hw hxw

/-! ## Finite sums over the row -/

/-- The volumes of finitely many maximal cubes of one generation add up to the volume of
their union, which lies inside the union of the whole row. -/
theorem sum_volume_le_volume_biUnion [NeZero d] (W : Set (Vec d)) (j r : ℤ)
    {S : Finset (Fin d → ℤ)} (hS : ↑S ⊆ maximalCellIndices W j r) :
    ∑ w ∈ S, volume (standardCell d r w) ≤
      volume (⋃ w ∈ maximalCellIndices W j r, standardCell d r w) := by
  rw [← measure_biUnion_finset ((pairwiseDisjoint_maximalCellIndices W j r).subset hS)
    fun w _ => measurableSet_standardCell r w]
  exact measure_mono (Set.biUnion_subset_biUnion_left hS)

/-- The row of generation `r` is finite: its cubes are disjoint, of equal positive volume,
and lie in a set of finite volume. -/
theorem finite_maximalCellIndices [NeZero d] {W : Set (Vec d)} (hW : volume W ≠ ⊤) (j r : ℤ) :
    (maximalCellIndices W j r).Finite := by
  by_contra hinf
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (volume_standardCell_pos (d := d) r 0).ne' hW
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have hsum : ∑ w ∈ S, volume (standardCell d r w) = n * volume (standardCell d r 0) := by
    rw [Finset.sum_congr rfl fun w _ => volume_standardCell r w, Finset.sum_const, hcard,
      nsmul_eq_mul, volume_standardCell]
  have := (sum_volume_le_volume_biUnion W j r hS).trans
    (volume_biUnion_maximalCellIndices_le_target W j r)
  rw [hsum] at this
  exact absurd hn (not_lt.mpr this)

/-- Conversion of a measure-form row bound `|⋃ row| ≤ C |W|` into the printed relative-volume
form `Σ |□_r| / |W| ≤ C`. -/
theorem sum_relVolume_le_of_volume_le [NeZero d] {W : Set (Vec d)} (hW0 : volume W ≠ 0)
    (hW : volume W ≠ ⊤) {j r : ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hle : volume (⋃ w ∈ maximalCellIndices W j r, standardCell d r w) ≤
      ENNReal.ofReal C * volume W) :
    ∑ w ∈ (finite_maximalCellIndices hW j r).toFinset,
      (volume (standardCell d r w)).toReal / (volume W).toReal ≤ C := by
  have hWpos : 0 < (volume W).toReal := ENNReal.toReal_pos hW0 hW
  have hsub : ↑(finite_maximalCellIndices hW j r).toFinset ⊆ maximalCellIndices W j r := by
    rw [Set.Finite.coe_toFinset]
  have h1 := (sum_volume_le_volume_biUnion W j r hsub).trans hle
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_sum fun w _ => volume_standardCell_ne_top r w] at h2
  rw [← Finset.sum_div, div_le_iff₀ hWpos]
  exact h2

/-! ## The printed constant -/

theorem natCast_rpow_three_halves (d : ℕ) :
    (d : ℝ) ^ ((3 : ℝ) / 2) = (d : ℝ) * Real.sqrt d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  calc (d : ℝ) ^ ((3 : ℝ) / 2) = (d : ℝ) ^ ((1 : ℝ) + 1 / 2) := by norm_num
    _ = (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_add hdpos _ _
    _ = (d : ℝ) * Real.sqrt d := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- `2d · (2 √d 3^{r+1}) · 3^{-j} = 12 d^{3/2} 3^{r-j}`. -/
theorem whitney_constant_identity (d : ℕ) (r j : ℤ) :
    2 * (d : ℝ) * (2 * (Real.sqrt d * (3 : ℝ) ^ (r + 1))) * (3 : ℝ) ^ (-j)
      = 12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (r - j) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [natCast_rpow_three_halves d, zpow_add_one₀ h3 r, zpow_sub₀ h3, zpow_neg, div_eq_mul_inv]
  ring

/-! ## `l.source.whitney`, the volume bound -/

/-- **`e.source.whitney.volumes`.**  Let `W = y + ⋄_j^q` with `|q⁻¹| ≤ 2`, and `r ≤ j`.
Then the maximal standard aligned cubes of generation `r` inside `W` (among those of
generation at most `j`) satisfy `Σ_{z ∈ 𝒵_r(W)} |□_r| / |W| ≤ 12 d^{3/2} 3^{r-j}`. -/
theorem sum_relVolume_maximalCells_le [NeZero d] {q : Mat d} (hq : InverseNormLE q 2)
    {j r : ℤ} (hrj : r ≤ j) (y : Vec d) :
    ∑ w ∈ (finite_maximalCellIndices (volume_adaptedCellTranslate_ne_top q j y) j r).toFinset,
        (volume (standardCell d r w)).toReal / (volume (adaptedCellTranslate q j y)).toReal ≤
      12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (r - j) := by
  have hW0 := (volume_adaptedCellTranslate_pos hq j y).ne'
  have hW := volume_adaptedCellTranslate_ne_top q j y
  have hd : (1 : ℝ) ≤ (d : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) (by norm_num)
  rcases hrj.lt_or_eq with hlt | rfl
  · rw [← whitney_constant_identity]
    exact sum_relVolume_le_of_volume_le hW0 hW (by positivity)
      (volume_biUnion_maximalCellIndices_le (by norm_num) hq hlt y)
  · refine (sum_relVolume_le_of_volume_le hW0 hW zero_le_one ?_).trans ?_
    · rw [ENNReal.ofReal_one, one_mul]
      exact volume_biUnion_maximalCellIndices_le_target _ _ _
    · rw [sub_self, zpow_zero, mul_one]
      linarith


/-! ## `l.source.whitney`, the full statement -/

/-- **`l.source.whitney` (Standard cubes inside an adapted cube).**  Let `W = y + ⋄_j^q` with
`|q⁻¹| ≤ 2` (the bound `e.rounded.grid.bounds` satisfied by `q = 𝒬(m)`), `y ∈ ℝ^d`, `j ∈ ℤ`.
The maximal standard aligned cubes contained in `W` with generations at most `j` are
pairwise disjoint subsets of `W` covering `W` up to a null set, each generation `r` has
finitely many of them, and `Σ_{z ∈ 𝒵_r(W)} |□_r| / |W| ≤ 12 d^{3/2} 3^{r-j}` for `r ≤ j`. -/
theorem source_whitney [NeZero d] {q : Mat d} (hq : InverseNormLE q 2) (j : ℤ) (y : Vec d) :
    (∀ p ∈ maximalCellPairs (adaptedCellTranslate q j y) j,
        standardCell d p.1 p.2 ⊆ adaptedCellTranslate q j y) ∧
      (maximalCellPairs (adaptedCellTranslate q j y) j).PairwiseDisjoint
        (fun p => standardCell d p.1 p.2) ∧
      volume (adaptedCellTranslate q j y \
        ⋃ p ∈ maximalCellPairs (adaptedCellTranslate q j y) j, standardCell d p.1 p.2) = 0 ∧
      ∀ r ≤ j, ∃ hfin : (maximalCellIndices (adaptedCellTranslate q j y) j r).Finite,
        ∑ w ∈ hfin.toFinset,
            (volume (standardCell d r w)).toReal / (volume (adaptedCellTranslate q j y)).toReal ≤
          12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (r - j) :=
  ⟨fun _ hp => hp.subset, pairwiseDisjoint_maximalCellPairs _ _,
    volume_diff_iUnion_maximalCells hq j y,
    fun _ hrj => ⟨_, sum_relVolume_maximalCells_le hq hrj y⟩⟩

end Homogenization.HighContrast.Geometry
