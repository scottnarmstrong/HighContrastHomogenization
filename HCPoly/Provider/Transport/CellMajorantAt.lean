/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CellMajorant

/-!
# The pathwise majorant family of an arbitrary target cell

This is the translated-target form of `Transport.exists_cell_majorant`.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The majorant family of one target cell.**  The maximal filling of the
target cell of the new grid at scales up to its own, together with the
below-start multiplier term, is exhibited as a family dominating the response
at every sample, symmetric at every sample, integrable, entrywise measurable,
with its mean computed in closed form, and with the centred decomposition of
the raw branch recorded almost surely. -/
theorem exists_cell_majorant_at [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ} (hd : 1 ≤ d) (hCd : 0 ≤ Cd) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {mu mu' : Mat d}
    (hmu : mu.PosDef) (hmu' : mu'.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar mu))
    (hq' : IsRoundedGrid jStar (roundedGrid jStar mu'))
    {Khop : ℝ} (hK : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop)
    {j : ℤ} (hjj : jStar ≤ j) (z : Fin d → ℤ)
    (hcontj : adaptedCellAt (roundedGrid jStar mu') j z ⊆ centeredCube d M) :
    ∃ (Z : ℤ → Finset (Fin d → ℤ)) (c : ℤ → ℝ) (Gm : CoeffSpace d → BlockMat d)
      (KG : BlockMat d),
      (∀ r, ↑(Z r) = fillingIndex (roundedGrid jStar mu) j
        (adaptedCellAt (roundedGrid jStar mu') j z) r) ∧
      (∀ r, ∀ w ∈ Z r, adaptedCellAt (roundedGrid jStar mu) r w ⊆
        adaptedCellAt (roundedGrid jStar mu') j z) ∧
      (∀ r, 0 ≤ c r) ∧
      (∀ r, ∀ w ∈ Z r,
        (volume (adaptedCellAt (roundedGrid jStar mu) r w)).toReal /
          (volume (adaptedCellAt (roundedGrid jStar mu') j z)).toReal = c r) ∧
      (∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) ≤ 1 ∧
      (∀ r ∈ Finset.Icc jStar j, r < j →
        (∑ _w ∈ Z r, c r) ≤
          6 * (d : ℝ) * Real.sqrt d * Khop * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) ∧
      (∀ a, toFullBlockMat
          (coarseBlock (adaptedCellAt (roundedGrid jStar mu') j z) a) ≤
        toFullBlockMat (Gm a)) ∧
      (∀ a, IsSymmetricBlockMat (Gm a)) ∧
      (∀ α β : BlockCoord d,
        AEStronglyMeasurable (fun a => toFullBlockMat (Gm a) α β) P) ∧
      Integrable (fun a => toFullBlockMat (Gm a)) P ∧
      (∫ a, toFullBlockMat (Gm a) ∂P) = toFullBlockMat KG ∧
      IsSymmetricBlockMat KG ∧
      toFullBlockMat KG =
        (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
            toFullBlockMat (adaptedMean P (roundedGrid jStar mu) r)) +
          (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu * zetaG g *
            (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P) • toFullBlockMat E ∧
      (∀ᵐ a ∂P, toFullBlockMat (blockSub (Gm a) KG) =
        (∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r, c r •
            toFullBlockMat (blockSub
              (coarseBlock (adaptedCellAt (roundedGrid jStar mu) r w) a)
              (adaptedMean P (roundedGrid jStar mu) r))) +
          (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu * zetaG g *
            (3 : ℝ) ^ (jStar - j) * (Y a - ∫ x, Y x ∂P)) • toFullBlockMat E) ∧
      toFullBlockMat (adaptedMean P (roundedGrid jStar mu') j) ≤
        toFullBlockMat KG := by
  classical
  set q : Mat d := roundedGrid jStar mu with hqdef
  set q' : Mat d := roundedGrid jStar mu' with hq'def
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hq'PD : q'.PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  set y0 : Vec d := adaptedCellCenter q' j z with hy0
  have hcell : adaptedCellAt q' j z = adaptedCellTranslate q' j y0 := by
    rw [hy0, ← adaptedCellAt_eq_adaptedCellTranslate]
  -- the maximal filling of the target at scales up to `j`
  obtain ⟨Z, hZidx, hZsub, -, hZvol, -, hZrow, -, -⟩ :=
    maximal_filling (p := q') (q := q) hq'PD hqPD j j y0
  set cbel : ℝ := 6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu *
    zetaG g * (3 : ℝ) ^ (jStar - j) with hcbel
  -- the pathwise a.e. domination of the target cell by the raw majorant
  have hcont' : ∀ r : ℤ, r < jStar → ∀ w ∈ Z r,
      adaptedCellAt q r w ⊆ centeredCube d M := fun r _ w hw =>
    (hZsub r w hw).trans (hcell ▸ hcontj)
  have hdom := coarseBlock_le_filling_rows_add_belowStart (P := P) (Ψ := Ψ) (K := K)
    (y := y0) hd hCd hg1 hE hEpd hY hmu hq hq'PD hK hjj hZidx hcont'
  simp only [← hcell] at hdom
  -- the uniform row weight
  set c : ℤ → ℝ := fun r => (ENNReal.ofReal (|q.det| * (3 : ℝ) ^ (r * (d : ℤ)))).toReal /
    (volume (adaptedCellAt q' j z)).toReal with hcdef
  have hcratio : ∀ r, ∀ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
      (volume (adaptedCellAt q' j z)).toReal = c r := by
    intro r w hw
    rw [hZvol r w hw, hcdef]
  have hc0 : ∀ r, 0 ≤ c r := fun r =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  -- the raw majorant
  set Graw : CoeffSpace d → BlockMat d := fun a => ofFullBlockMat
    ((∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellAt q' j z)).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
      (cbel * Y a) • toFullBlockMat E) with hGraw
  have hdom' : ∀ᵐ a ∂P, toFullBlockMat (coarseBlock (adaptedCellAt q' j z) a) ≤
      toFullBlockMat (Graw a) := by
    filter_upwards [hdom] with a ha
    rw [hGraw]
    simpa only [toFullBlockMat_ofFullBlockMat] using ha
  -- symmetry of the raw branch
  have hEfullsym : (toFullBlockMat E).IsSymm := isSymm_toFullBlockMat_of_isSymmetricBlockMat hE
  have hcellsym : ∀ (a : CoeffSpace d) (r : ℤ) (w : Fin d → ℤ),
      (toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)).IsSymm := fun a r w =>
    isSymm_toFullBlockMat_of_isSymmetricBlockMat
      (isSymmetricBlockMat_coarseBlock (adaptedCellAt q r w) a)
  have hGrawsym : ∀ a, IsSymmetricBlockMat (Graw a) := by
    intro a
    simp only [hGraw]
    refine isSymmetricBlockMat_of_isSymm ?_
    ext γ δ
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine congrArg₂ (· + ·) ?_ (congrArg _ (hEfullsym.apply γ δ))
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w _ =>
      congrArg _ ((hcellsym a r w).apply γ δ)
  -- the family with domination at every sample
  obtain ⟨Gm, hGmdom, hGmsym, hGmae⟩ := exists_pointwise_majorant hdom'
    (fun a => isSymmetricBlockMat_coarseBlock (adaptedCellAt q' j z) a) hGrawsym
  -- entrywise measurability
  have hYint : Integrable Y P := integrable_of_isWindowMultiplier hY
  have hcellentry : ∀ (r : ℤ) (w : Fin d → ℤ) (α β : BlockCoord d), AEStronglyMeasurable
      (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) α β) P := by
    intro r w α β
    have h := Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hqPD r w α β
    simpa only [toFullBlockMat_eq_blockMatEntry] using h
  have hGrawentry : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (Graw a) α β) P := by
    intro α β
    simp only [hGraw, toFullBlockMat_ofFullBlockMat, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine AEStronglyMeasurable.add ?_ ?_
    · exact Finset.aestronglyMeasurable_fun_sum _ fun r _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun w _ => (hcellentry r w α β).const_mul _
    · exact (hYint.aestronglyMeasurable.const_mul cbel).mul_const _
  have hGmentry : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (Gm a) α β) P := by
    intro α β
    refine (hGrawentry α β).congr ?_
    filter_upwards [hGmae] with a ha
    rw [ha]
  -- integrability of the cells and of the raw branch
  have hcellcube : ∀ r, ∀ w ∈ Z r, adaptedCellAt q r w ⊆ centeredCube d M :=
    fun r w hw => ((hZsub r w hw).trans (hcell ▸ hcontj))
  have hcellint : ∀ r, ∀ w ∈ Z r, HasIntegrableCoarseBlock P (adaptedCellAt q r w) :=
    fun r w hw => hasIntegrableCoarseBlock_adaptedCellTranslate hY hmu hq r
      (adaptedCellCenter q r w) (hcellcube r w hw)
  have hGrawfun : (fun a => toFullBlockMat (Graw a)) = fun a =>
      (∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellAt q' j z)).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
      (cbel * Y a) • toFullBlockMat E := by
    funext a
    simp only [hGraw, toFullBlockMat_ofFullBlockMat]
  have hGrawint : Integrable (fun a => toFullBlockMat (Graw a)) P := by
    refine integrable_of_entries fun α β => ?_
    simp only [hGraw, toFullBlockMat_ofFullBlockMat, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine Integrable.add ?_ ?_
    · exact integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun w hw =>
        ((integrable_toFullBlockMat (hcellint r w hw)).eval α).eval β |>.const_mul _
    · exact (hYint.const_mul cbel).mul_const _
  have hGmint : Integrable (fun a => toFullBlockMat (Gm a)) P := by
    refine hGrawint.congr ?_
    filter_upwards [hGmae] with a ha
    rw [ha]
  -- the mean of the raw branch, with the stationarity collapse
  have hmeanraw : ∫ a, toFullBlockMat (Graw a) ∂P =
      (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
          toFullBlockMat (adaptedMean P q r)) +
        (cbel * ∫ a, Y a ∂P) • toFullBlockMat E := by
    ext γ δ
    rw [entry_integral hGrawint γ δ]
    simp only [hGraw, toFullBlockMat_ofFullBlockMat, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    have hsumEntry : Integrable (fun a => ∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellAt q' j z)).toReal) *
        toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) γ δ) P :=
      integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun w hw =>
        ((integrable_toFullBlockMat (hcellint r w hw)).eval γ).eval δ |>.const_mul _
    have hbelEntry : Integrable (fun a => cbel * Y a * toFullBlockMat E γ δ) P :=
      (hYint.const_mul cbel).mul_const _
    rw [integral_add hsumEntry hbelEntry]
    have hYEentry : ∫ a, cbel * Y a * toFullBlockMat E γ δ ∂P =
        cbel * (∫ a, Y a ∂P) * toFullBlockMat E γ δ := by
      simp only [mul_assoc]
      rw [integral_const_mul, integral_mul_const]
    rw [hYEentry]
    refine congrArg₂ (· + ·) ?_ rfl
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun w hw =>
      ((integrable_toFullBlockMat (hcellint r w hw)).eval γ).eval δ |>.const_mul _]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hjr : jStar ≤ r := (Finset.mem_Icc.mp hr).1
    have hmeas : HasMeasurableCoarseBlock P (adaptedCell q r) :=
      Recurrence.hasMeasurableCoarseBlock_adaptedCell P hqPD r
    rw [integral_finsetSum _ fun w hw =>
      ((integrable_toFullBlockMat (hcellint r w hw)).eval γ).eval δ |>.const_mul _]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [integral_const_mul, hcratio r w hw,
      ← entry_integral (integrable_toFullBlockMat (hcellint r w hw)) γ δ,
      ← toFullBlockMat_annealedBlock (hcellint r w hw),
      Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hq hjr hmeas w]
  -- the annealed majorant
  set KG : BlockMat d := ofFullBlockMat
    ((∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
        toFullBlockMat (adaptedMean P q r)) +
      (cbel * ∫ a, Y a ∂P) • toFullBlockMat E) with hKG
  have hKGfull : toFullBlockMat KG =
      (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
          toFullBlockMat (adaptedMean P q r)) +
        (cbel * ∫ a, Y a ∂P) • toFullBlockMat E := by
    rw [hKG, toFullBlockMat_ofFullBlockMat]
  have hKGsym : IsSymmetricBlockMat KG := by
    rw [hKG]
    refine isSymmetricBlockMat_of_isSymm ?_
    ext γ δ
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine congrArg₂ (· + ·) ?_ (congrArg _ (hEfullsym.apply γ δ))
    exact Finset.sum_congr rfl fun r _ => congrArg _
      ((isSymm_toFullBlockMat_of_isSymmetricBlockMat
        (Recurrence.isSymmetricBlockMat_adaptedMean P q r)).apply γ δ)
  have hGmmean : ∫ a, toFullBlockMat (Gm a) ∂P = toFullBlockMat KG := by
    rw [hKGfull, ← hmeanraw]
    refine integral_congr_ae ?_
    filter_upwards [hGmae] with a ha
    rw [ha]
  -- the total mass of the filling
  have hmass : (∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) ≤ 1 := by
    have h := sum_relative_volume_le_one (p := q') (q := q) hq'PD hqPD
      (R := Finset.Icc jStar j) hZidx
    calc ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r
        = ∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate q' j y0)).toReal :=
          Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w hw => by
            rw [← hcratio r w hw, hcell]
      _ ≤ 1 := h
  -- the boundary rows
  have hrowb : ∀ r ∈ Finset.Icc jStar j, r < j → (∑ _w ∈ Z r, c r) ≤
      6 * (d : ℝ) * Real.sqrt d * Khop * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
    intro r hr hrj
    have h := hZrow r hrj
    have hnorm : ‖q'⁻¹ * q‖ ≤ Khop := ((norm_inv_mul_le_gridRatio hd q q').1).trans hK
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hK0 : (0 : ℝ) ≤ Khop :=
      le_trans (le_trans zero_le_one (one_le_gridRatio q q')) hK
    have hz0 : (0 : ℝ) ≤ (3 : ℝ) ^ (r - j : ℤ) := le_of_lt (by positivity)
    have hcoef0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ *
        (3 : ℝ) ^ (r - j : ℤ) := by
      have : (0 : ℝ) ≤ ‖q'⁻¹ * q‖ := norm_nonneg _
      positivity
    have hvT : volume (adaptedCellTranslate q' j y0) ≠ ⊤ :=
      volume_adaptedCellTranslate_ne_top q' j y0
    have htr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvT) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef0] at htr
    have htsum : (∑ w ∈ Z r, volume (adaptedCellAt q r w)).toReal =
        ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal :=
      ENNReal.toReal_sum fun w hw => by
        rw [hZvol r w hw]
        exact ENNReal.ofReal_ne_top
    have hvT0 : (0 : ℝ) < (volume (adaptedCellTranslate q' j y0)).toReal :=
      ENNReal.toReal_pos (volume_adaptedCellTranslate_ne_zero hq'PD j y0) hvT
    have hdiv : (∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal) /
        (volume (adaptedCellTranslate q' j y0)).toReal ≤
        6 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ * (3 : ℝ) ^ (r - j : ℤ) := by
      rw [div_le_iff₀ hvT0]
      calc ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal
          = (∑ w ∈ Z r, volume (adaptedCellAt q r w)).toReal := htsum.symm
        _ ≤ _ := htr
    have hzr : ((3 : ℝ) ^ (r - j : ℤ) : ℝ) = (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) (r - j)]
      push_cast
      ring_nf
    calc ∑ _w ∈ Z r, c r
        = ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate q' j y0)).toReal :=
          Finset.sum_congr rfl fun w hw => by rw [← hcratio r w hw, hcell]
      _ = (∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal) /
            (volume (adaptedCellTranslate q' j y0)).toReal := by
          rw [Finset.sum_div]
      _ ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ * (3 : ℝ) ^ (r - j : ℤ) := hdiv
      _ ≤ 6 * (d : ℝ) * Real.sqrt d * Khop * (3 : ℝ) ^ (r - j : ℤ) := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm
            (by positivity : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d)) hz0
          calc 6 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ * (3 : ℝ) ^ (r - j : ℤ)
              = 6 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ * (3 : ℝ) ^ (r - j : ℤ) := rfl
            _ ≤ 6 * (d : ℝ) * Real.sqrt d * Khop * (3 : ℝ) ^ (r - j : ℤ) := by
                have h1 : 6 * (d : ℝ) * Real.sqrt d * ‖q'⁻¹ * q‖ ≤
                    6 * (d : ℝ) * Real.sqrt d * Khop := mul_le_mul_of_nonneg_left hnorm
                  (by positivity)
                exact mul_le_mul_of_nonneg_right h1 hz0
      _ = 6 * (d : ℝ) * Real.sqrt d * Khop * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
          rw [hzr]
  -- the centred decomposition of the raw branch
  have hcentred : ∀ᵐ a ∂P, toFullBlockMat (blockSub (Gm a) KG) =
      (∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r, c r •
          toFullBlockMat (blockSub
            (coarseBlock (adaptedCellAt q r w) a)
            (adaptedMean P q r))) +
        (cbel * (Y a - ∫ x, Y x ∂P)) • toFullBlockMat E := by
    filter_upwards [hGmae] with a ha
    have hfullsub : ∀ A B : BlockMat d, toFullBlockMat (blockSub A B) =
        toFullBlockMat A - toFullBlockMat B := by
      intro A B
      ext α β
      rw [Recurrence.toFullBlockMat_blockSub_apply, Matrix.sub_apply]
    rw [hfullsub, ha]
    simp only [hGraw, hKG, toFullBlockMat_ofFullBlockMat]
    have hterm : ∀ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r, c r •
        toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
          (adaptedMean P q r)) =
        (∑ w ∈ Z r, ((volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellAt q' j z)).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) -
          (∑ _w ∈ Z r, c r) • toFullBlockMat (adaptedMean P q r) := by
      intro r hr
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hfullsub, smul_sub, hcratio r w hw]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    have hbel : (cbel * (Y a - ∫ x, Y x ∂P)) • toFullBlockMat E =
        (cbel * Y a) • toFullBlockMat E - (cbel * ∫ x, Y x ∂P) • toFullBlockMat E := by
      rw [mul_sub, sub_smul]
    rw [hbel]
    abel
  -- the annealed exhaustion: the target mean is below the annealed majorant
  have hEjKG : toFullBlockMat (adaptedMean P q' j) ≤ toFullBlockMat KG := by
    have h := adaptedMean_le_filling_rows (P := P) (Ψ := Ψ) (K := K) (n := j) (j := j)
      (z := z) hd hCd hg1 hE hEpd hP hY hmu hmu' hq hq' hK hjj hjj
      (by
        intro r
        rw [hcell]
        exact hZidx r)
      (fun r w hw => hcellcube r w hw)
      hcontj
    rw [hKGfull]
    refine le_trans h (le_of_eq ?_)
    refine congrArg₂ (· + ·) ?_ rfl
    refine Finset.sum_congr rfl fun r hr => ?_
    refine congrArg₂ (· • ·) ?_ rfl
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hcratio r w hw]
  exact ⟨Z, c, Gm, KG, (fun r => by rw [hcell]; exact hZidx r),
    fun r w hw => (hZsub r w hw).trans_eq hcell.symm, hc0, hcratio, hmass, hrowb,
    hGmdom, hGmsym, hGmentry, hGmint, hGmmean, hKGsym, hKGfull, hcentred, hEjKG⟩

end

end Transport
end HighContrast
end Homogenization


