import HCPoly.Entry.Geometry.MaximalCells
import HCPoly.Setup.Geometry

/-!
# The maximal cubes exhaust `W`

The remaining measure-theoretic half of `l.source.whitney`: for
`W = y + q □_j` with `q` invertible, the maximal standard aligned cubes of generation at
most `j` contained in `W` cover `W` up to a Lebesgue-null set.

The null set is the union `⋃ k : ℤ, gridFaces d k` of all grid faces of all generations,
which is null because `ℤ` is countable.  Off that set, every `x ∈ W` lies in a standard
aligned cube of every generation, and cubes of very negative generation are small enough to
fit inside `W` (which is open); a maximal cube through `x` then exists.
-/

open Homogenization.HighContrast (adaptedCellTranslate standardCell)
namespace Homogenization.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

/-- **The maximal cubes exhaust `W` up to a null set.**  For `W = y + q □_j` with `q`
invertible, the maximal standard aligned cubes of generation `≤ j` inside `W` cover `W`
up to a Lebesgue-null set. -/
theorem volume_diff_iUnion_maximalCells [NeZero d] {q : Mat d} {K : ℝ}
    (hq : InverseNormLE q K) (j : ℤ) (y : Vec d) :
    volume (adaptedCellTranslate q j y \
      ⋃ p ∈ maximalCellPairs (adaptedCellTranslate q j y) j, standardCell d p.1 p.2) = 0 := by
  refine measure_mono_null (t := ⋃ k : ℤ, gridFaces d k) ?_
    (measure_iUnion_null fun k => volume_gridFaces k)
  rintro x ⟨hxW, hxU⟩
  by_contra hxN
  -- `W` is open, so some ball about `x` lies in `W`
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_adaptedCellTranslate hq.isUnit j y) x hxW
  -- choose a generation `k ≤ j` with `3 ^ k < ε`
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((3 : ℝ) ^ j / ε) (by norm_num : (1 : ℝ) < 3)
  set k : ℤ := j - (n : ℤ) with hk
  have hkj : k ≤ j := by omega
  have h3k : (3 : ℝ) ^ k < ε := by
    rw [hk, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast,
      div_lt_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ n)]
    exact (mul_comm ((3 : ℝ) ^ n) ε) ▸ (div_lt_iff₀ hε).mp hn
  -- `x` avoids the generation-`k` grid faces, so it lies in a generation-`k` cube
  have hxk : x ∉ gridFaces d k := fun h => hxN (Set.mem_iUnion.mpr ⟨k, h⟩)
  obtain ⟨w, hw⟩ := exists_mem_standardCell_of_not_mem_gridFaces hxk
  -- that cube is small, hence contained in `W`
  have hsub : standardCell d k w ⊆ adaptedCellTranslate q j y :=
    (standardCell_subset_ball hw).trans ((Metric.ball_subset_ball h3k.le).trans hball)
  obtain ⟨k', w', hmax, hx'⟩ := exists_isMaximalCellIn_of_isCellIn ⟨hkj, hsub⟩ hw
  exact hxU (Set.mem_iUnion₂.mpr ⟨(k', w'), hmax, hx'⟩)

end Homogenization.HighContrast.Geometry
