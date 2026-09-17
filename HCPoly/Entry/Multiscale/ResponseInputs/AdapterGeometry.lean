import HCPoly.Entry.Multiscale.ResponseInputs.AdapterBasic

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (adaptedCellCenter)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate standardCell)
namespace Homogenization.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- The capped Whitney row bound uses only the inverse norm of the relative
matrix. In particular its constant is linear in that norm. -/
theorem lower_row_volume {d : ℕ} [NeZero d] {q q' : Mat d} {K : ℝ}
    (hq : IsUnit q) (hq' : IsUnit q') (hK : 0 ≤ K)
    (hInv : InverseNormLE (q⁻¹ * q') K)
    (j cap r : ℤ) (hr : r < cap) (y : Vec d) :
    ∑ _z ∈ (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (volume_adaptedCellTranslate_ne_top q' j y) cap r).toFinset,
      (volume (adaptedCell q r)).toReal / (volume (adaptedCellTranslate q' j y)).toReal ≤
        (6 * (d : ℝ) * K * Real.sqrt d) * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
  classical
  let V := adaptedCellTranslate (q⁻¹ * q') j (matVecMul q⁻¹ y)
  have hvol := volume_le_of_near_complement hK hInv
    (j := j) (y := matVecMul q⁻¹ y)
    (A := ⋃ w ∈ maximalCellIndices V cap r, standardCell d r w)
    (s := Real.sqrt d * (3 : ℝ) ^ (r + 1)) (by positivity)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact hw.subset hxw)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact exists_not_mem_of_mem_maximalCell hr hw hxw)
  have hc : 2 * (d : ℝ) * (K * (Real.sqrt d * (3 : ℝ) ^ (r + 1))) *
      (3 : ℝ) ^ (-j) = (6 * (d : ℝ) * K * Real.sqrt d) *
        (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
    rw [← Int.cast_sub, Real.rpow_intCast, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0),
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, div_eq_mul_inv]
    ring
  rw [hc] at hvol
  have hsum := sum_relVolume_le_of_volume_le
    (volume_adaptedCellTranslate_pos hInv j (matVecMul q⁻¹ y)).ne'
    (volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y))
    (by positivity : 0 ≤ (6 * (d : ℝ) * K * Real.sqrt d) *
      (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) hvol
  simp_rw [← adaptedCell_relVolume_eq_standard_preimage hq hq' j r y] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum ⊢
  have hcard :
      (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (volume_adaptedCellTranslate_ne_top q' j y) cap r).toFinset.card =
      (finite_maximalCellIndices
        (volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y)) cap r).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _
        (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
          (volume_adaptedCellTranslate_ne_top q' j y) cap r),
      ← Set.ncard_eq_toFinset_card _
        (finite_maximalCellIndices
          (volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y)) cap r),
      ncard_maximalAdaptedCellCenters_eq_preimage hq,
      preimage_matVecMul_adaptedCellTranslate_eq hq]
  rw [hcard]
  exact hsum

/-- A norm bound `‖q'⁻¹ * q‖ ≤ K` transfers to an `InverseNormLE` bound on `q⁻¹ * q'` itself, by
cancelling the two grids and applying the operator-norm inequality to the inverse product. -/
theorem relative_inverse_bound {d : ℕ} {q q' : Mat d} {K : ℝ}
    (hq : IsUnit q) (hq' : IsUnit q') (hK : ‖q'⁻¹ * q‖ ≤ K) :
    InverseNormLE (q⁻¹ * q') K := by
  intro v
  have hcancel : (q'⁻¹ * q) * (q⁻¹ * q') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc q q⁻¹ q',
      Matrix.mul_nonsing_inv q ((Matrix.isUnit_iff_isUnit_det q).mp hq),
      Matrix.one_mul, Matrix.nonsing_inv_mul q' ((Matrix.isUnit_iff_isUnit_det q').mp hq')]
  have hb := vecNormSq_mulVec_le_opNorm (q'⁻¹ * q) (Matrix.mulVec (q⁻¹ * q') v)
  rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hK 2) (vecNormSq_nonneg _))

/-- The volume-ratio weights of the maximal adapted `q`-cells tiling a `q'`-cell `W` are
summable and sum to one: the maximal cells are pairwise disjoint and their union covers `W` up
to a null set. -/
theorem maximal_mass {d : ℕ} [NeZero d]
    (q q' : Mat d) (hq : IsUnit q) (hq' : IsUnit q') (n cap : ℤ) (y : Vec d) :
    let W := adaptedCellTranslate q' n y
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    let w := fun i : I => (volume (adaptedCellAtCenter q i.1.1 i.1.2)).toReal / (volume W).toReal
    Summable w ∧ (∑' i, w i) = 1 := by
  intro W I w
  let s := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q cap p.1 p.2}
  have hsub : ∀ i ∈ s, adaptedCellAtCenter q i.1 i.2 ⊆ W := fun _ hi => hi.1.2
  have hdis := pairwiseDisjoint_maximalAdaptedCellPairs W q hq cap
  have hnull := volume_diff_iUnion_maximalAdaptedCells_of_isOpen hq
    (isOpen_adaptedCellTranslate hq' n y) cap
  have hWfin : volume W ≠ ⊤ := volume_adaptedCellTranslate_ne_top q' n y
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hmeas (i) (_hi : i ∈ s) : MeasurableSet (adaptedCellAtCenter q i.1 i.2) :=
    (isOpen_adaptedCellTranslate hq i.1 (adaptedCellCenter q i.1 i.2)).measurableSet
  have hw : Summable w := summable_volumeRatio (s := s) (W := W) (U := fun i => adaptedCellAtCenter q i.1 i.2)
    hmeas hsub hdis
  have hW0 : (volume W).toReal ≠ 0 := by
    dsimp [W]
    rw [volume_adaptedCellTranslate_toReal]
    have hdq : q'.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q').mp hq').ne_zero
    positivity
  exact ⟨hw, Source.tsum_volumeRatio_eq_one (Set.to_countable s)
    (W := W) (U := fun i => adaptedCellAtCenter q i.1 i.2) hW0 hmeas hsub hdis hnull⟩

end Homogenization.HighContrast.Multiscale.Adapter
