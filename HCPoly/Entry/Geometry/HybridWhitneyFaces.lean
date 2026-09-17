import HCPoly.Entry.Geometry.AffineGridDistortion

/-!
# Packed adapted cells and the null grid seams

Support for construction (ii) of `l.two.grid.whitney`.
The uncovered set includes internal open-cell seams. Off the new-grid
faces its points are interior points; all pointwise boundary arguments must
retain this null exception. No replacement of the uncovered set is made.
-/

open Homogenization.HighContrast (adaptedCellCenter gridRatio)
open Homogenization.HighContrast (adaptedCellTranslate standardCell)
namespace Homogenization.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

/-- The packed index family is the cap row of the actual maximal family. -/
theorem contained_adaptedCellIndices_eq_cap [NeZero d] {q : Mat d}
    (hq : IsUnit q) (W : Set (Vec d)) (n : ℤ) :
    {w : Fin d → ℤ | adaptedCellAtCenter q n w ⊆ W} =
      maximalAdaptedCellIndices W q n n := by
  ext w
  exact ⟨fun h => (isMaximalAdaptedCellIn_iff_parent_not_subset hq n n w).mpr
    ⟨le_rfl, h, Or.inl rfl⟩, fun h => h.1.2⟩

/-- Positive-volume disjoint cap cells form a finite family inside finite volume. -/
theorem finite_contained_adaptedCellIndices [NeZero d] {q : Mat d}
    (hq : IsUnit q) {W : Set (Vec d)} (hW : volume W ≠ ⊤) (n : ℤ) :
    {w : Fin d → ℤ | adaptedCellAtCenter q n w ⊆ W}.Finite := by
  rw [contained_adaptedCellIndices_eq_cap hq]
  exact finite_maximalAdaptedCellIndices_of_volume_ne_top hq hW n n

/-- Distinct indices in an invertible grid give disjoint open cells. -/
theorem adaptedCellAtCenter_disjoint_of_ne {q : Mat d} (hq : IsUnit q)
    (n : ℤ) {w v : Fin d → ℤ} (hwv : w ≠ v) :
    Disjoint (adaptedCellAtCenter q n w) (adaptedCellAtCenter q n v) := by
  rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell]
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have h := matVecMul_injective_of_isUnit q hq hba
  exact Set.disjoint_left.mp (standardCell_disjoint_of_ne n hwv) ha (h ▸ hb)

/-- An open adapted cell is contained in a set exactly when it is contained
in its interior; consequently the maximal predicate is unchanged. -/
theorem isMaximalAdaptedCellIn_interior_iff {q : Mat d} (hq : IsUnit q)
    (W : Set (Vec d)) (n r : ℤ) (w : Fin d → ℤ) :
    IsMaximalAdaptedCellIn (interior W) q n r w ↔
      IsMaximalAdaptedCellIn W q n r w := by
  have hc (k : ℤ) (v : Fin d → ℤ) :
      IsAdaptedCellIn (interior W) q n k v ↔ IsAdaptedCellIn W q n k v := by
    exact and_congr_right fun _ =>
      (isOpen_adaptedCellTranslate hq k (adaptedCellCenter q k v)).subset_interior_iff
  unfold IsMaximalAdaptedCellIn
  simp_rw [hc]

/-- Outside the affine generation faces there is an actual open adapted cell. -/
theorem exists_mem_adaptedCellAtCenter_of_not_mem_gridFaces {q : Mat d}
    (hq : IsUnit q) (n : ℤ) {x : Vec d}
    (hx : x ∉ matVecMul q '' gridFaces d n) :
    ∃ w : Fin d → ℤ, x ∈ adaptedCellAtCenter q n w := by
  let u := matVecMul q⁻¹ x
  have hqu : matVecMul q u = x := by
    dsimp [u]
    rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv q ((Matrix.isUnit_iff_isUnit_det q).mp hq),
      Matrix.one_mulVec]
  have hu : u ∉ gridFaces d n := fun h => hx ⟨u, h, hqu⟩
  obtain ⟨w, hw⟩ := exists_mem_standardCell_of_not_mem_gridFaces hu
  refine ⟨w, ?_⟩
  rw [adaptedCellAtCenter_eq_affine_standardCell]
  exact ⟨u, hw, hqu⟩

/-- An unpacked cell cannot meet any cell in the packed generation. -/
theorem adaptedCellAtCenter_disjoint_adaptedCoveredPart {q : Mat d}
    (hq : IsUnit q) (W : Set (Vec d)) (n : ℤ) (w : Fin d → ℤ)
    (hw : ¬ adaptedCellAtCenter q n w ⊆ W) :
    Disjoint (adaptedCellAtCenter q n w) (adaptedCoveredPart W q n) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hxC
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hxC
  have hwv : w ≠ v := by
    rintro rfl
    exact hw hv
  exact Set.disjoint_left.mp (adaptedCellAtCenter_disjoint_of_ne hq n hwv) hx hxv

/-- Internal packed seams can remain uncovered, but away from the new-grid
faces every uncovered point is interior. This is the a.e. reading required
by the strip argument in `l.two.grid.whitney`. -/
theorem adaptedUncoveredPart_diff_interior_subset_gridFaces {q : Mat d}
    (hq : IsUnit q) {W : Set (Vec d)} (hW : IsOpen W) (n : ℤ) :
    adaptedUncoveredPart W q n \ interior (adaptedUncoveredPart W q n) ⊆
      matVecMul q '' gridFaces d n := by
  rintro x ⟨hxU, hxI⟩
  by_contra hxN
  obtain ⟨w, hxw⟩ := exists_mem_adaptedCellAtCenter_of_not_mem_gridFaces hq n hxN
  have hw : ¬ adaptedCellAtCenter q n w ⊆ W := by
    intro hw
    exact hxU.2 (Set.mem_iUnion₂.mpr ⟨w, hw, hxw⟩)
  have hsub : W ∩ adaptedCellAtCenter q n w ⊆ adaptedUncoveredPart W q n := by
    rintro z ⟨hzW, hzw⟩
    exact ⟨hzW, Set.disjoint_left.mp
      (adaptedCellAtCenter_disjoint_adaptedCoveredPart hq W n w hw) hzw⟩
  exact hxI (interior_maximal hsub
    (hW.inter (isOpen_adaptedCellTranslate hq n (adaptedCellCenter q n w))) ⟨hxU.1, hxw⟩)

/-- The interior exhausts the uncovered part modulo new-grid faces. -/
theorem volume_adaptedUncoveredPart_diff_interior {q : Mat d}
    (hq : IsUnit q) {W : Set (Vec d)} (hW : IsOpen W) (n : ℤ) :
    volume (adaptedUncoveredPart W q n \ interior (adaptedUncoveredPart W q n)) = 0 := by
  refine measure_mono_null
    ((adaptedUncoveredPart_diff_interior_subset_gridFaces hq hW n).trans
      (Set.image_mono (Set.subset_iUnion (fun k : ℤ => gridFaces d k) n)))
    (volume_image_iUnion_gridFaces q)

/-- The packed family and the actual maximal old cells exhaust an open parent.
The uncovered set itself need not be open. This includes the empty packed family. -/
theorem volume_diff_adaptedCoveredPart_union_maximalCells [NeZero d]
    {q q' : Mat d} (hq : IsUnit q) (hq' : IsUnit q')
    {W : Set (Vec d)} (hW : IsOpen W) (n : ℤ) :
    volume (W \ (adaptedCoveredPart W q' n ∪
      ⋃ p ∈ {p : ℤ × (Fin d → ℤ) |
        IsMaximalAdaptedCellIn (adaptedUncoveredPart W q' n) q n p.1 p.2},
        adaptedCellAtCenter q p.1 p.2)) = 0 := by
  let U := adaptedUncoveredPart W q' n
  refine measure_mono_null (t := (U \ interior U) ∪
    (interior U \ ⋃ p ∈ {p : ℤ × (Fin d → ℤ) |
      IsMaximalAdaptedCellIn (interior U) q n p.1 p.2},
      adaptedCellAtCenter q p.1 p.2)) ?_
    (measure_union_null (volume_adaptedUncoveredPart_diff_interior hq' hW n)
      (volume_diff_iUnion_maximalAdaptedCells_of_isOpen hq isOpen_interior n))
  rintro x ⟨hxW, hx⟩
  have hxU : x ∈ U := ⟨hxW, fun h => hx (Or.inl h)⟩
  by_cases hxI : x ∈ interior U
  · right
    refine ⟨hxI, ?_⟩
    intro hxM
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxM
    exact hx (Or.inr (Set.mem_iUnion₂.mpr ⟨p,
      (isMaximalAdaptedCellIn_interior_iff hq U n p.1 p.2).mp hp, hxp⟩))
  · exact Or.inl ⟨hxU, hxI⟩

/-- Points in lattice-neighbor cells are at distance at most twice the
usual cell diameter. The hypothesis also allows diagonal neighbors. -/
theorem sum_sq_sub_le_of_mem_neighbor_standardCells {n : ℤ}
    {w v : Fin d → ℤ} (hwv : ∀ i, |(w i : ℝ) - (v i : ℝ)| ≤ 1)
    {x y : Vec d} (hx : x ∈ standardCell d n w) (hy : y ∈ standardCell d n v) :
    ∑ i, (x i - y i) ^ 2 ≤ (2 * Real.sqrt d * (3 : ℝ) ^ n) ^ 2 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hterm (i : Fin d) : (x i - y i) ^ 2 ≤ (2 * (3 : ℝ) ^ n) ^ 2 := by
    obtain ⟨hxlo, hxhi⟩ := mem_standardCell_iff.mp hx i
    obtain ⟨hylo, hyhi⟩ := mem_standardCell_iff.mp hy i
    obtain ⟨hwvlo, hwvhi⟩ := abs_le.mp (hwv i)
    have hlo : -(2 * (3 : ℝ) ^ n) ≤ x i - y i := by
      nlinarith only [hxlo, hyhi, hwvlo, h3]
    have hhi : x i - y i ≤ 2 * (3 : ℝ) ^ n := by
      nlinarith only [hxhi, hylo, hwvhi, h3]
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (abs_le.mpr ⟨hlo, hhi⟩)
  calc
    ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin d, (2 * (3 : ℝ) ^ n) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (2 * Real.sqrt d * (3 : ℝ) ^ n) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      ring

/-- A packed face is exposed when its lattice neighbor across that face is
unpacked. Only cubes with such a face enter this union; interior packed
seams contribute nothing to the estimate. -/
theorem volume_exposed_adaptedCells_preimage_le_of_gridRatio [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n : ℤ) (y : Vec d) :
    let W := adaptedCellTranslate q j y
    let E := {w : Fin d → ℤ | adaptedCellAtCenter q' n w ⊆ W ∧
      ∃ (i : Fin d) (b : Bool), ¬ adaptedCellAtCenter q' n
        (Function.update w i (w i + if b then 1 else -1)) ⊆ W}
    volume (⋃ w ∈ E, standardCell d n w) ≤
      ENNReal.ofReal ((4 * (d : ℝ) * K₀ * Real.sqrt d) *
        (3 : ℝ) ^ ((n : ℝ) - (j : ℝ))) * volume ((matVecMul q') ⁻¹' W) := by
  intro W E
  have hKswap : gridRatio q' q ≤ K₀ := by
    simpa only [gridRatio, add_right_comm] using hK
  have hpre := preimage_matVecMul_adaptedCellTranslate_eq hq' (q' := q) j y
  have hvol := volume_le_of_near_complement (le_trans zero_le_one hK₀)
    (inverseNormLE_relative_of_gridRatio hd hq' hq hKswap)
    (j := j) (y := matVecMul q'⁻¹ y)
    (A := ⋃ w ∈ E, standardCell d n w)
    (s := 2 * Real.sqrt d * (3 : ℝ) ^ n) (by positivity)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      rw [← hpre]
      exact (standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q' n w).mpr hw.1 hxw)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨i, b, hnot⟩ := hw.2
      let v := Function.update w i (w i + if b then 1 else -1)
      have hv : ¬ standardCell d n v ⊆ (matVecMul q') ⁻¹' W :=
        fun h => hnot ((standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q' n v).mp h)
      obtain ⟨z, hzv, hzW⟩ := Set.not_subset.mp hv
      refine ⟨z, by rwa [← hpre], ?_⟩
      apply sum_sq_sub_le_of_mem_neighbor_standardCells (w := w) (v := v) ?_ hxw hzv
      intro k
      by_cases hk : k = i
      · subst k
        cases b <;> norm_num [v, Int.cast_add]
      · simp only [v, Function.update_of_ne hk, sub_self, abs_zero, zero_le_one])
  have hc : 2 * (d : ℝ) * (K₀ * (2 * Real.sqrt d * (3 : ℝ) ^ n)) *
      (3 : ℝ) ^ (-j) = (4 * (d : ℝ) * K₀ * Real.sqrt d) *
        (3 : ℝ) ^ ((n : ℝ) - (j : ℝ)) := by
    rw [← Int.cast_sub, Real.rpow_intCast,
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, div_eq_mul_inv]
    ring
  rwa [hc, ← hpre] at hvol

/-- There are at most `C(d,K₀) 3^((d-1)(j-n))` packed cubes with exposed
faces. The cap family is proved finite inside this theorem. -/
theorem ncard_exposed_adaptedCells_le_of_gridRatio [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n : ℤ) (y : Vec d) :
    let W := adaptedCellTranslate q j y
    let E := {w : Fin d → ℤ | adaptedCellAtCenter q' n w ⊆ W ∧
      ∃ (i : Fin d) (b : Bool), ¬ adaptedCellAtCenter q' n
        (Function.update w i (w i + if b then 1 else -1)) ⊆ W}
    (E.ncard : ℝ) ≤ ((4 * (d : ℝ) * K₀ * Real.sqrt d) *
      ((Nat.factorial d : ℝ) * K₀ ^ d)) *
        (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (n : ℝ))) := by
  classical
  intro W E
  have hE : E.Finite := (finite_contained_adaptedCellIndices hq'
    (volume_adaptedCellTranslate_ne_top q j y) n).subset (fun _ h => h.1)
  have hdis : (hE.toFinset : Set (Fin d → ℤ)).PairwiseDisjoint
      (fun w => standardCell d n w) :=
    fun _ _ _ _ hne => standardCell_disjoint_of_ne n hne
  have hvolrow := measure_biUnion_finset (μ := volume) hdis
    (fun w _ => measurableSet_standardCell n w)
  have hroweq : (volume (⋃ w ∈ E, standardCell d n w)).toReal =
      (E.ncard : ℝ) * ((3 : ℝ) ^ n) ^ d := by
    have h := hvolrow
    simp only [hE.mem_toFinset] at h
    rw [h, ENNReal.toReal_sum (fun w _ => volume_standardCell_ne_top n w)]
    simp only [volume_standardCell, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3 ^ n),
      Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card E hE]
  let V := adaptedCellTranslate (q'⁻¹ * q) j (matVecMul q'⁻¹ y)
  let A : ℝ := 4 * (d : ℝ) * K₀ * Real.sqrt d
  let D : ℝ := (Nat.factorial d : ℝ) * K₀ ^ d
  have hV : volume V ≠ ⊤ := volume_adaptedCellTranslate_ne_top _ _ _
  have hbound := volume_exposed_adaptedCells_preimage_le_of_gridRatio
    hd hK₀ hq hq' hK j n y
  change volume (⋃ w ∈ E, standardCell d n w) ≤
    ENNReal.ofReal (A * (3 : ℝ) ^ ((n : ℝ) - (j : ℝ))) *
      volume ((matVecMul q') ⁻¹' W) at hbound
  rw [preimage_matVecMul_adaptedCellTranslate_eq hq'] at hbound
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hbound
  rw [hroweq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by dsimp [A]; positivity),
    volume_adaptedCellTranslate_toReal] at hreal
  have hdet : |(q'⁻¹ * q).det| ≤ D := abs_det_inv_mul_comm_le_gridRatio_of_le hd hK
  have hmass : (E.ncard : ℝ) * ((3 : ℝ) ^ n) ^ d ≤
      (A * D) * ((3 : ℝ) ^ ((n : ℝ) - (j : ℝ)) * ((3 : ℝ) ^ j) ^ d) := by
    calc
      _ ≤ (A * (3 : ℝ) ^ ((n : ℝ) - (j : ℝ))) *
          (|(q'⁻¹ * q).det| * ((3 : ℝ) ^ j) ^ d) := hreal
      _ ≤ (A * (3 : ℝ) ^ ((n : ℝ) - (j : ℝ))) *
          (D * ((3 : ℝ) ^ j) ^ d) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdet (by positivity)) (by dsimp [A]; positivity)
      _ = _ := by ring
  have hscale : (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (n : ℝ))) *
      ((3 : ℝ) ^ n) ^ d =
      (3 : ℝ) ^ ((n : ℝ) - (j : ℝ)) * ((3 : ℝ) ^ j) ^ d := by
    rw [← Real.rpow_intCast (3 : ℝ) n, ← Real.rpow_intCast (3 : ℝ) j,
      ← Real.rpow_natCast ((3 : ℝ) ^ (n : ℝ)) d,
      ← Real.rpow_natCast ((3 : ℝ) ^ (j : ℝ)) d,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d)).mp
  change (E.ncard : ℝ) * ((3 : ℝ) ^ n) ^ d ≤
    ((A * D) * (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (n : ℝ)))) * ((3 : ℝ) ^ n) ^ d
  rw [mul_assoc, hscale]
  exact hmass

/-- In its own invertible grid coordinates the packed union is
exactly the packed union of standard cells. -/
theorem preimage_adaptedCoveredPart_self {q : Mat d} (hq : IsUnit q)
    (W : Set (Vec d)) (n : ℤ) :
    (matVecMul q) ⁻¹' adaptedCoveredPart W q n =
      adaptedCoveredPart ((matVecMul q) ⁻¹' W) (1 : Mat d) n := by
  have hc (w : Fin d → ℤ) : adaptedCellAtCenter (1 : Mat d) n w = standardCell d n w := by
    have hid : matVecMul (1 : Mat d) = (fun v => v) :=
      funext fun v => by rw [matVecMul_eq_mulVec, Matrix.one_mulVec]
    rw [adaptedCellAtCenter_eq_affine_standardCell, hid]
    exact Set.image_id' _
  have hp (w : Fin d → ℤ) : (matVecMul q) ⁻¹' adaptedCellAtCenter q n w = standardCell d n w := by
    rw [adaptedCellAtCenter_eq_affine_standardCell,
      Set.preimage_image_eq _ (matVecMul_injective_of_isUnit q hq)]
  ext x
  simp only [Set.mem_preimage, adaptedCoveredPart, Set.mem_iUnion, Set.mem_ofPred_eq, hc]
  simp_rw [← standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q n,
    ← Set.mem_preimage, hp]

end Homogenization.HighContrast.Geometry
