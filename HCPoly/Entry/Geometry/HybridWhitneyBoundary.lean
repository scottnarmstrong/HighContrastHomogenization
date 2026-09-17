import HCPoly.Entry.Geometry.HybridWhitneyFaces
import HCPoly.Entry.Geometry.AffineGridDistortion

/-!
# The outer strip of the hybrid Whitney construction

The uncovered part of `l.two.grid.whitney` lies in the outer
strip modulo the explicitly excluded new-grid faces. All metric estimates
use relative coordinates; neither absolute matrix norm is bounded.
-/

open Homogenization.HighContrast (gridRatio)
open Homogenization.HighContrast (adaptedCellTranslate standardCell)
namespace Homogenization.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

/-- In the packed grid's coordinates an uncovered point off grid faces
shares a generation-`n` cell with a point outside the parent. -/
theorem exists_not_mem_of_mem_uncovered_preimage (q : Mat d)
    (W : Set (Vec d)) (n : ℤ) {x : Vec d}
    (hx : matVecMul q x ∈ adaptedUncoveredPart W q n)
    (hxN : x ∉ gridFaces d n) :
    ∃ x', x' ∉ (matVecMul q) ⁻¹' W ∧
      ∑ i, (x i - x' i) ^ 2 ≤ (Real.sqrt d * (3 : ℝ) ^ n) ^ 2 := by
  obtain ⟨w, hxw⟩ := exists_mem_standardCell_of_not_mem_gridFaces hxN
  have hw : ¬ standardCell d n w ⊆ (matVecMul q) ⁻¹' W := by
    intro hw
    have hwW := (standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q n w).mp hw
    have hxA : matVecMul q x ∈ adaptedCellAtCenter q n w := by
      rw [adaptedCellAtCenter_eq_affine_standardCell]
      exact ⟨x, hxw, rfl⟩
    exact hx.2 (Set.mem_iUnion₂.mpr ⟨w, hwW, hxA⟩)
  obtain ⟨x', hx'w, hx'W⟩ := Set.not_subset.mp hw
  refine ⟨x', hx'W, ?_⟩
  calc
    ∑ i, (x i - x' i) ^ 2 ≤ (d : ℝ) * ((3 : ℝ) ^ n) ^ 2 :=
      sum_sq_sub_le_of_mem_standardCell hxw hx'w
    _ = (Real.sqrt d * (3 : ℝ) ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

/-- The whole uncovered volume satisfies the cap-scale outer-strip estimate.
The proof removes the new-grid faces before applying the pointwise strip
lemma, then restores them using their zero measure. -/
theorem volume_adaptedUncoveredPart_le_of_gridRatio [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n : ℤ) (y : Vec d) :
    volume (adaptedUncoveredPart (adaptedCellTranslate q j y) q' n) ≤
      ENNReal.ofReal ((2 * (d : ℝ) * K₀ * Real.sqrt d) *
        (3 : ℝ) ^ ((n : ℝ) - (j : ℝ))) * volume (adaptedCellTranslate q j y) := by
  let W := adaptedCellTranslate q j y
  let U := adaptedUncoveredPart W q' n
  let A := ((matVecMul q') ⁻¹' U) \ gridFaces d n
  have hKswap : gridRatio q' q ≤ K₀ := by
    simpa only [gridRatio, add_right_comm] using hK
  have hInv := inverseNormLE_relative_of_gridRatio hd hq' hq hKswap
  have hpre := preimage_matVecMul_adaptedCellTranslate_eq hq' (q' := q) j y
  have hvol := volume_le_of_near_complement (le_trans zero_le_one hK₀) hInv
    (j := j) (y := matVecMul q'⁻¹ y) (A := A)
    (s := Real.sqrt d * (3 : ℝ) ^ n) (by positivity)
    (by
      intro x hx
      rw [← hpre]
      exact hx.1.1)
    (by
      intro x hx
      obtain ⟨x', hx'W, hdist⟩ :=
        exists_not_mem_of_mem_uncovered_preimage q' W n hx.1 hx.2
      refine ⟨x', ?_, hdist⟩
      rwa [← hpre])
  have hAvol : volume A = volume ((matVecMul q') ⁻¹' U) :=
    measure_sdiff_null (volume_gridFaces n)
  have hc : 2 * (d : ℝ) * (K₀ * (Real.sqrt d * (3 : ℝ) ^ n)) *
      (3 : ℝ) ^ (-j) = (2 * (d : ℝ) * K₀ * Real.sqrt d) *
        (3 : ℝ) ^ ((n : ℝ) - (j : ℝ)) := by
    rw [← Int.cast_sub, Real.rpow_intCast,
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, div_eq_mul_inv]
    ring
  rw [hAvol, hc, ← hpre] at hvol
  have hJac (S : Set (Vec d)) :
      volume S = ENNReal.ofReal |q'.det| * volume ((matVecMul q') ⁻¹' S) := by
    have hs : matVecMul q' '' ((matVecMul q') ⁻¹' S) = S :=
      Set.image_preimage_eq S (Matrix.mulVec_surjective_iff_isUnit.mpr hq')
    calc
      volume S = volume (matVecMul q' '' ((matVecMul q') ⁻¹' S)) := by rw [hs]
      _ = _ := by
        simpa only [zero_add] using
          volume_image_affine q' (0 : Vec d) ((matVecMul q') ⁻¹' S)
  calc
    volume U = ENNReal.ofReal |q'.det| * volume ((matVecMul q') ⁻¹' U) := hJac U
    _ ≤ ENNReal.ofReal |q'.det| *
        (ENNReal.ofReal ((2 * (d : ℝ) * K₀ * Real.sqrt d) *
          (3 : ℝ) ^ ((n : ℝ) - (j : ℝ))) * volume ((matVecMul q') ⁻¹' W)) :=
      mul_le_mul_right hvol _
    _ = ENNReal.ofReal ((2 * (d : ℝ) * K₀ * Real.sqrt d) *
        (3 : ℝ) ^ ((n : ℝ) - (j : ℝ))) * volume W := by
      rw [mul_left_comm, ← hJac W]

/-- Exact volume of a width-`t` rectangular neighborhood of a packed face.
The other coordinates are enlarged by `t`, so this includes its end caps. -/
theorem volume_standard_face_neighborhood (n : ℤ) (w : Fin d → ℤ)
    (i : Fin d) (b : Bool) (t : ℝ) :
    let a : ℝ := ((w i : ℝ) + if b then 1 / 2 else -1 / 2) * (3 : ℝ) ^ n
    volume (Set.pi Set.univ
      (Function.update
        (fun k : Fin d => Set.Icc (((w k : ℝ) - 1 / 2) * (3 : ℝ) ^ n - t)
          (((w k : ℝ) + 1 / 2) * (3 : ℝ) ^ n + t))
        i (Set.Icc (a - t) (a + t)))) =
      ENNReal.ofReal (2 * t) * ENNReal.ofReal ((3 : ℝ) ^ n + 2 * t) ^ (d - 1) := by
  classical
  intro a
  rw [volume_pi_pi]
  let f (k : Fin d) := volume ((Function.update
    (fun k : Fin d => Set.Icc (((w k : ℝ) - 1 / 2) * (3 : ℝ) ^ n - t)
      (((w k : ℝ) + 1 / 2) * (3 : ℝ) ^ n + t)) i (Set.Icc (a - t) (a + t))) k)
  change ∏ k, f k = _
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  have hi : f i = ENNReal.ofReal (2 * t) := by
    dsimp [f]
    rw [Function.update_self, Real.volume_Icc]
    congr 1
    ring
  rw [hi]
  congr 1
  have hk (k : Fin d) (hk : k ∈ Finset.univ.erase i) :
      f k = ENNReal.ofReal ((3 : ℝ) ^ n + 2 * t) := by
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    dsimp [f]
    rw [Function.update_of_ne hki, Real.volume_Icc]
    congr 1
    ring
  rw [Finset.prod_congr rfl hk, Finset.prod_const]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

/-- At `r ≤ n` the end-cap contribution is absorbed into a constant
independent of both generations; the coefficient may depend on the width
multiplier `c`, as required after relative matrix distortion. -/
theorem volume_standard_face_neighborhood_le (n r : ℤ) (hr : r ≤ n)
    (w : Fin d → ℤ) (i : Fin d) (b : Bool) {c : ℝ} (hc : 0 ≤ c) :
    let t := c * (3 : ℝ) ^ r
    let a : ℝ := ((w i : ℝ) + if b then 1 / 2 else -1 / 2) * (3 : ℝ) ^ n
    volume (Set.pi Set.univ
      (Function.update
        (fun k : Fin d => Set.Icc (((w k : ℝ) - 1 / 2) * (3 : ℝ) ^ n - t)
          (((w k : ℝ) + 1 / 2) * (3 : ℝ) ^ n + t))
        i (Set.Icc (a - t) (a + t)))) ≤
      ENNReal.ofReal ((2 * c * (1 + 2 * c) ^ (d - 1)) *
        (3 : ℝ) ^ r * ((3 : ℝ) ^ n) ^ (d - 1)) := by
  change volume _ ≤ _
  rw [volume_standard_face_neighborhood]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h3 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hr
  have hside : (3 : ℝ) ^ n + 2 * (c * (3 : ℝ) ^ r) ≤
      (1 + 2 * c) * (3 : ℝ) ^ n := by
    have h := mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
    linarith only [h]
  calc
    2 * (c * (3 : ℝ) ^ r) * ((3 : ℝ) ^ n + 2 * (c * (3 : ℝ) ^ r)) ^ (d - 1) ≤
        2 * (c * (3 : ℝ) ^ r) * ((1 + 2 * c) * (3 : ℝ) ^ n) ^ (d - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hside _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- A finite closest-cell argument finds an exposed packed face near an
uncovered point whenever a packed point is nearby. Internal packed seams
are excluded by the explicit generation-face hypothesis. -/
theorem exposed_face_near_uncovered_point {d : ℕ} [NeZero d]
    (W : Set (Vec d)) (hW : volume W ≠ ⊤) (n : ℤ)
    (x y : Vec d) (hxN : x ∉ gridFaces d n)
    (hx : x ∉ adaptedCoveredPart W (1 : Mat d) n)
    (hy : y ∈ adaptedCoveredPart W (1 : Mat d) n)
    (s : ℝ) (hs : 0 ≤ s) (hxy : ∀ k, |x k - y k| ≤ s) :
    ∃ w : Fin d → ℤ, adaptedCellAtCenter (1 : Mat d) n w ⊆ W ∧
      ∃ (i : Fin d) (b : Bool),
        (¬ adaptedCellAtCenter (1 : Mat d) n
          (Function.update w i (w i + if b then 1 else -1)) ⊆ W) ∧
        (let t := (d : ℝ) * s
         let a : ℝ := ((w i : ℝ) + if b then 1 / 2 else -1 / 2) * (3 : ℝ) ^ n
         x ∈ Set.pi Set.univ
           (Function.update
             (fun k : Fin d => Set.Icc (((w k : ℝ) - 1 / 2) * (3 : ℝ) ^ n - t)
               (((w k : ℝ) + 1 / 2) * (3 : ℝ) ^ n + t))
             i (Set.Icc (a - t) (a + t)))) := by
  classical
  have hF := finite_contained_adaptedCellIndices (q := (1 : Mat d)) isUnit_one hW n
  obtain ⟨v, hv, hyv⟩ := Set.mem_iUnion₂.mp hy
  let score (w : Fin d → ℤ) : ℝ :=
    ∑ k, max (|x k - (w k : ℝ) * (3 : ℝ) ^ n| - (3 : ℝ) ^ n / 2) 0
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image hF.toFinset score
    ⟨v, hF.mem_toFinset.mpr hv⟩
  have ha : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hd (u : Fin d → ℤ) (k : Fin d) :
      max (|x k - (u k : ℝ) * (3 : ℝ) ^ n| - (3 : ℝ) ^ n / 2) 0 ≤ score u := by
    dsimp [score]
    exact Finset.single_le_sum
      (f := fun k : Fin d => max (|x k - (u k : ℝ) * (3 : ℝ) ^ n| - (3 : ℝ) ^ n / 2) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ k)
  have hscorepos : 0 < score w := by
    by_contra h
    have hle : score w ≤ 0 := le_of_not_gt h
    have hxstd : x ∈ standardCell d n w := by
      rw [mem_standardCell_iff]
      intro k
      have habs : |x k - (w k : ℝ) * (3 : ℝ) ^ n| ≤ (3 : ℝ) ^ n / 2 := by
        have h := (le_max_left _ _).trans ((hd w k).trans hle)
        linarith only [h]
      obtain ⟨hlo, hhi⟩ := abs_le.mp habs
      constructor
      · apply lt_of_le_of_ne (by linarith only [hlo])
        intro heq
        apply hxN
        refine Set.mem_iUnion₂.mpr ⟨k, w k - 1, ?_⟩
        change x k = (((w k - 1 : ℤ) : ℝ) + 1 / 2) * (3 : ℝ) ^ n
        rw [← heq]
        push_cast
        ring
      · apply lt_of_le_of_ne (by linarith only [hhi])
        intro heq
        exact hxN (Set.mem_iUnion₂.mpr ⟨k, w k, heq⟩)
    have hxadapt : x ∈ adaptedCellAtCenter (1 : Mat d) n w := by
      rw [adaptedCellAtCenter_eq_affine_standardCell]
      refine ⟨x, hxstd, ?_⟩
      exact Matrix.one_mulVec x
    exact hx (Set.mem_iUnion₂.mpr ⟨w, hF.mem_toFinset.mp hw, hxadapt⟩)
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun _ _ => le_max_right _ _)).mp hscorepos
  have houtside : (3 : ℝ) ^ n / 2 < |x i - (w i : ℝ) * (3 : ℝ) ^ n| := by
    have h := (lt_max_iff.mp hi).resolve_right (lt_irrefl 0)
    linarith only [h]
  obtain ⟨b, hb⟩ : ∃ b : Bool,
      if b then (w i : ℝ) * (3 : ℝ) ^ n + (3 : ℝ) ^ n / 2 < x i
      else x i < (w i : ℝ) * (3 : ℝ) ^ n - (3 : ℝ) ^ n / 2 := by
    rcases lt_abs.mp houtside with h | h
    · exact ⟨true, by dsimp; linarith only [h]⟩
    · exact ⟨false, by dsimp; linarith only [h]⟩
  let u := Function.update w i (w i + if b then 1 else -1)
  have hshift (a c z : ℝ) (ha : 0 < a) (hz : c + a / 2 < z) :
      max (|z - (c + a)| - a / 2) 0 < max (|z - c| - a / 2) 0 := by
    have hzabs : |z - c| = z - c := abs_of_pos (by linarith only [ha, hz])
    have hzmax : max (|z - c| - a / 2) 0 = z - c - a / 2 := by
      rw [hzabs, max_eq_left (by linarith only [hz])]
    rw [hzmax]
    apply max_lt
    · rcases le_total (c + a) z with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        linarith only [ha]
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]
        linarith only [hz]
    · linarith only [hz]
  have hdi : max (|x i - (u i : ℝ) * (3 : ℝ) ^ n| - (3 : ℝ) ^ n / 2) 0 <
      max (|x i - (w i : ℝ) * (3 : ℝ) ^ n| - (3 : ℝ) ^ n / 2) 0 := by
    cases b
    · have h := hshift ((3 : ℝ) ^ n) (-((w i : ℝ) * (3 : ℝ) ^ n)) (-x i)
        ha (by dsimp at hb; linarith only [hb])
      have heq : -x i - (-((w i : ℝ) * (3 : ℝ) ^ n) + (3 : ℝ) ^ n) =
          -(x i - ((w i : ℝ) - 1) * (3 : ℝ) ^ n) := by ring
      have heq' : -x i - -((w i : ℝ) * (3 : ℝ) ^ n) =
          -(x i - (w i : ℝ) * (3 : ℝ) ^ n) := by ring
      rw [heq, heq', abs_neg, abs_neg] at h
      simpa only [u, Bool.false_eq_true, ↓reduceIte, Function.update_self,
        Int.cast_add, Int.cast_neg, Int.cast_one, sub_eq_add_neg] using h
    · have h := hshift ((3 : ℝ) ^ n) ((w i : ℝ) * (3 : ℝ) ^ n) (x i) ha hb
      simpa only [u, ↓reduceIte, Function.update_self, Int.cast_add, Int.cast_one,
        add_mul, one_mul] using h
  have hless : score u < score w := by
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : k = i
      · subst k; exact hdi.le
      · simp only [u, Function.update_of_ne hk, le_refl]
    · exact ⟨i, Finset.mem_univ i, hdi⟩
  have hu : ¬ adaptedCellAtCenter (1 : Mat d) n u ⊆ W := by
    intro hu
    exact (not_lt_of_ge (hmin u (hF.mem_toFinset.mpr hu))) hless
  have hyvstd : y ∈ standardCell d n v := by
    rw [adaptedCellAtCenter_eq_affine_standardCell] at hyv
    rcases hyv with ⟨z, hz, hzy⟩
    have hzy' : z = y := by simpa only [matVecMul_eq_mulVec, Matrix.one_mulVec] using hzy
    exact hzy' ▸ hz
  have hscorebound : score w ≤ (d : ℝ) * s := by
    apply (hmin v (hF.mem_toFinset.mpr hv)).trans
    calc
      score v ≤ ∑ _k : Fin d, s := by
        apply Finset.sum_le_sum
        intro k _
        obtain ⟨hylo, hyhi⟩ := mem_standardCell_iff.mp hyvstd k
        have hyabs : |y k - (v k : ℝ) * (3 : ℝ) ^ n| ≤ (3 : ℝ) ^ n / 2 := by
          rw [abs_le]
          constructor <;> linarith only [hylo, hyhi]
        have htri := abs_sub_le (x k) (y k) ((v k : ℝ) * (3 : ℝ) ^ n)
        exact max_le (by linarith only [htri, hxy k, hyabs]) hs
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨w, hF.mem_toFinset.mp hw, i, b, hu, ?_⟩
  dsimp only
  intro k _
  have hdist : |x k - (w k : ℝ) * (3 : ℝ) ^ n| ≤
      (3 : ℝ) ^ n / 2 + (d : ℝ) * s := by
    have h := (le_max_left _ _).trans ((hd w k).trans hscorebound)
    linarith only [h]
  have ht : 0 ≤ (d : ℝ) * s := mul_nonneg (Nat.cast_nonneg d) hs
  by_cases hk : k = i
  · subst k
    rw [Function.update_self]
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdist
    cases b <;> dsimp at hb ⊢ <;> constructor <;> linarith only [hb, hlo, hhi, ht]
  · rw [Function.update_of_ne hk]
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdist
    constructor <;> linarith only [hlo, hhi]

/-- The affine neighborhoods of all faces in a finite cube family have the
expected width times surface-volume bound, including overlaps and end caps. -/
theorem volume_iUnion_affine_face_neighborhoods_le (P : Mat d)
    (F : Finset (Fin d → ℤ)) (n r : ℤ) (hr : r ≤ n) {c : ℝ} (hc : 0 ≤ c) :
    let t := c * (3 : ℝ) ^ r
    let B (w : Fin d → ℤ) (i : Fin d) (b : Bool) :=
      let a : ℝ := ((w i : ℝ) + if b then 1 / 2 else -1 / 2) * (3 : ℝ) ^ n
      Set.pi Set.univ (Function.update
        (fun k : Fin d => Set.Icc (((w k : ℝ) - 1 / 2) * (3 : ℝ) ^ n - t)
          (((w k : ℝ) + 1 / 2) * (3 : ℝ) ^ n + t)) i (Set.Icc (a - t) (a + t)))
    volume (⋃ w ∈ F, ⋃ i : Fin d, ⋃ b : Bool, matVecMul P '' B w i b) ≤
      ENNReal.ofReal ((F.card : ℝ) * (2 * d) * |P.det| *
        (2 * c * (1 + 2 * c) ^ (d - 1)) * (3 : ℝ) ^ r * ((3 : ℝ) ^ n) ^ (d - 1)) := by
  intro t B
  let v : ℝ := |P.det| * (2 * c * (1 + 2 * c) ^ (d - 1)) *
    (3 : ℝ) ^ r * ((3 : ℝ) ^ n) ^ (d - 1)
  have hbox (w : Fin d → ℤ) (i : Fin d) (b : Bool) :
      volume (matVecMul P '' B w i b) ≤ ENNReal.ofReal v := by
    calc
      _ = ENNReal.ofReal |P.det| * volume (B w i b) := by
        simpa only [zero_add] using volume_image_affine P (0 : Vec d) (B w i b)
      _ ≤ ENNReal.ofReal |P.det| *
          ENNReal.ofReal ((2 * c * (1 + 2 * c) ^ (d - 1)) *
            (3 : ℝ) ^ r * ((3 : ℝ) ^ n) ^ (d - 1)) :=
        mul_le_mul_right (volume_standard_face_neighborhood_le n r hr w i b hc) _
      _ = _ := by rw [← ENNReal.ofReal_mul (abs_nonneg _)]; congr 1; dsimp [v]; ring
  have hi (w : Fin d → ℤ) : volume (⋃ i : Fin d, ⋃ b : Bool, matVecMul P '' B w i b) ≤
      ∑ _i : Fin d, ∑ _b : Bool, ENNReal.ofReal v := by
    refine (measure_iUnion_fintype_le volume _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (measure_iUnion_fintype_le volume _).trans (Finset.sum_le_sum fun b _ => hbox w i b)
  calc
    _ ≤ ∑ _w ∈ F, ∑ _i : Fin d, ∑ _b : Bool, ENNReal.ofReal v :=
      (measure_biUnion_finset_le F _).trans (Finset.sum_le_sum fun w _ => hi w)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool,
        nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast F.card, ← ENNReal.ofReal_natCast d,
        ← ENNReal.ofReal_natCast 2, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg d),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg F.card)]
      congr 1
      dsimp [v]
      ring

end Homogenization.HighContrast.Geometry
