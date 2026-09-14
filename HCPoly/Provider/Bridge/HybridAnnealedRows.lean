/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.HybridPathwiseRows

/-!
# Annealed reverse-hybrid rows

Stationarity turns the packed cells into the new-grid mean and the selected
cells in the uncovered strip into old-grid means.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- The reverse hybrid exhaustion after expectation.  Packed cells collapse to
the new-grid mean, selected cells collapse to old-grid means, and the remaining
below-alignment rows form the displayed multiplier term. -/
theorem adaptedMean_le_hybrid_rows [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mq mq' : Mat d} (hmq : mq.PosDef) (hmq' : mq'.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar mq))
    (hq' : IsRoundedGrid jStar (roundedGrid jStar mq'))
    {n l : ℤ} (hjn : jStar ≤ n)
    (hcont : adaptedCell (roundedGrid jStar mq) (n + l) ⊆ centeredCube d M)
    (Zp : Finset (Fin d → ℤ)) (Z : ℤ → Finset (Fin d → ℤ))
    (hZp : ↑Zp = Transport.hybridPackingIndex (roundedGrid jStar mq') n
      (adaptedCell (roundedGrid jStar mq) (n + l)))
    (hZ : ∀ r, ↑(Z r) = Transport.fillingIndex (roundedGrid jStar mq) n
      (Transport.hybridStrip (roundedGrid jStar mq') n
        (adaptedCell (roundedGrid jStar mq) (n + l))) r) :
    toFullBlockMat (adaptedMean P (roundedGrid jStar mq) (n + l)) ≤
      (∑ w ∈ Zp,
        ((volume (adaptedCellAt (roundedGrid jStar mq') n w)).toReal /
          (volume (adaptedCell (roundedGrid jStar mq) (n + l))).toReal) •
            toFullBlockMat (adaptedMean P (roundedGrid jStar mq') n)) +
        (∑ r ∈ Finset.Icc jStar n,
          (∑ w ∈ Z r,
            (volume (adaptedCellAt (roundedGrid jStar mq) r w)).toReal /
              (volume (adaptedCell (roundedGrid jStar mq) (n + l))).toReal) •
            toFullBlockMat (adaptedMean P (roundedGrid jStar mq) r)) +
        (3 * (2 * (d : ℝ) * Real.sqrt d +
              (2 * (d : ℝ) * Real.sqrt d) *
                (2 * (d : ℝ) * Real.sqrt d) * 2 *
                  (1 + 6 * Real.sqrt d) ^ (d - 1)) *
            gridRatio (roundedGrid jStar mq) (roundedGrid jStar mq') *
            boundaryConst Cd g mq * zetaG g *
            (3 : ℝ) ^ (jStar - (n + l)) * (∫ a, Y a ∂P)) •
          toFullBlockMat E := by
  classical
  let q := roundedGrid jStar mq
  let q' := roundedGrid jStar mq'
  let W := adaptedCell q (n + l)
  have hqpd : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hq'pd : q'.PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  have hzero : adaptedCellTranslate q (n + l) 0 = W := by
    simp [W, adaptedCellTranslate]
  have hcontW : W ⊆ centeredCube d M := by
    simpa only [W, q] using hcont
  have hcell : ∀ r, ∀ w ∈ Z r, adaptedCellAt q r w ⊆ centeredCube d M := by
    intro r w hw
    have hw' : w ∈ Transport.fillingIndex q n (Transport.hybridStrip q' n W) r := by
      rw [← hZ r]
      exact Finset.mem_coe.mpr hw
    exact (Transport.adaptedCellAt_subset_of_mem_fillingIndex hw').trans
      (Transport.hybridStrip_subset.trans hcont)
  have hpackcell : ∀ w ∈ Zp, adaptedCellAt q' n w ⊆ centeredCube d M := by
    intro w hw
    have hw' : w ∈ Transport.hybridPackingIndex q' n W := by
      rw [← hZp]
      exact Finset.mem_coe.mpr hw
    exact (Transport.adaptedCellAt_subset_of_mem_fillingIndex hw').trans hcont
  let Cg : ℝ := 2 * (d : ℝ) * Real.sqrt d +
    (2 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ) * Real.sqrt d) * 2 *
      (1 + 6 * Real.sqrt d) ^ (d - 1)
  have hraw : ∀ᵐ a ∂P,
      toFullBlockMat (coarseBlock W a) ≤
        (∑ w ∈ Zp,
          ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)) +
        (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
          ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
        (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
          (3 : ℝ) ^ (jStar - (n + l)) * Y a) • toFullBlockMat E := by
    filter_upwards [hY.adapted_primal] with a ha
    simpa only [q, q', W, Cg] using coarseBlock_le_hybrid_rows
      hd hCd hg hE hEpd hY hmq hq hq' hjn hcont Zp Z hZp hZ a ha
  have hWint : HasIntegrableCoarseBlock P W := by
    rw [← hzero]
    exact Transport.hasIntegrableCoarseBlock_adaptedCellTranslate hY hmq hq
      (n + l) 0 (by rw [hzero]; exact hcontW)
  have hpackint : ∀ w ∈ Zp, HasIntegrableCoarseBlock P (adaptedCellAt q' n w) :=
    fun w hw => Transport.hasIntegrableCoarseBlock_adaptedCellTranslate hY hmq' hq' n
      (adaptedCellCenter q' n w) (hpackcell w hw)
  have hrowint : ∀ r ∈ Finset.Icc jStar n, ∀ w ∈ Z r,
      HasIntegrableCoarseBlock P (adaptedCellAt q r w) := fun r _ w hw =>
    Transport.hasIntegrableCoarseBlock_adaptedCellTranslate hY hmq hq r
      (adaptedCellCenter q r w) (hcell r w hw)
  have hYint := Transport.integrable_of_isWindowMultiplier hY
  let Fp : CoeffSpace d → FullBlockMat d := fun a => ∑ w ∈ Zp,
    ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)
  let Fr : CoeffSpace d → FullBlockMat d := fun a =>
    ∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
      ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)
  let FG : CoeffSpace d → FullBlockMat d := fun a =>
    (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
      (3 : ℝ) ^ (jStar - (n + l)) * Y a) • toFullBlockMat E
  -- The scalar-entry route around the ambient `FullBlockMat d` norm instance: every
  -- integrability fact below is proved one real-valued entry at a time and then
  -- reassembled, so no combinator ever has to compare two `ContinuousENorm` instances
  -- on the matrix type itself.
  have hentry : ∀ U : Set (Vec d), HasIntegrableCoarseBlock P U → ∀ i j : BlockCoord d,
      Integrable (fun a => toFullBlockMat (coarseBlock U a) i j) P := fun U hU i j => by
    simpa only [toFullBlockMat_eq_blockMatEntry] using hU i j
  have hscaledEntry : ∀ (c : ℝ) (U : Set (Vec d)), HasIntegrableCoarseBlock P U →
      ∀ i j : BlockCoord d,
      Integrable (fun a => (c • toFullBlockMat (coarseBlock U a)) i j) P := by
    intro c U hU i j
    have heq : (fun a => (c • toFullBlockMat (coarseBlock U a)) i j) =
        fun a => c * toFullBlockMat (coarseBlock U a) i j :=
      funext fun a => by rw [Matrix.smul_apply, smul_eq_mul]
    rw [heq]
    exact (hentry U hU i j).const_mul c
  have hscaled : ∀ (c : ℝ) (U : Set (Vec d)), HasIntegrableCoarseBlock P U →
      Integrable (fun a => c • toFullBlockMat (coarseBlock U a)) P :=
    fun c U hU => integrable_of_entries (hscaledEntry c U hU)
  have hpackEntry : ∀ i j : BlockCoord d, Integrable (fun a => Fp a i j) P := by
    intro i j
    have heq : (fun a => Fp a i j) = fun a => ∑ w ∈ Zp,
        ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) *
          toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) i j := by
      funext a
      dsimp only [Fp]
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun w _ => by rw [Matrix.smul_apply, smul_eq_mul]
    rw [heq]
    exact integrable_finsetSum Zp fun w hw =>
      (hentry _ (hpackint w hw) i j).const_mul
        ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal)
  have hrowEntry : ∀ i j : BlockCoord d, Integrable (fun a => Fr a i j) P := by
    intro i j
    have heq : (fun a => Fr a i j) = fun a =>
        ∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
          ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) *
            toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) i j := by
      funext a
      dsimp only [Fr]
      rw [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun w _ => by rw [Matrix.smul_apply, smul_eq_mul]
    rw [heq]
    exact integrable_finsetSum (Finset.Icc jStar n) fun r hr =>
      integrable_finsetSum (Z r) fun w hw =>
        (hentry _ (hrowint r hr w hw) i j).const_mul
          ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal)
  have hGEntry : ∀ i j : BlockCoord d, Integrable (fun a => FG a i j) P := by
    intro i j
    have heq : (fun a => FG a i j) = fun a =>
        (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
          (3 : ℝ) ^ (jStar - (n + l)) * Y a) * toFullBlockMat E i j := by
      funext a
      dsimp only [FG]
      rw [Matrix.smul_apply, smul_eq_mul]
    rw [heq]
    exact (hYint.const_mul (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
      (3 : ℝ) ^ (jStar - (n + l)))).mul_const (toFullBlockMat E i j)
  have hpackI : Integrable Fp P := integrable_of_entries hpackEntry
  have hrowI : Integrable Fr P := integrable_of_entries hrowEntry
  have hGI : Integrable FG P := integrable_of_entries hGEntry
  have hsumI : Integrable (fun a => Fp a + Fr a) P := by
    refine integrable_of_entries fun i j => ?_
    have heq : (fun a => (Fp a + Fr a) i j) = fun a => Fp a i j + Fr a i j := by
      funext a; rw [Matrix.add_apply]
    rw [heq]
    exact (hpackEntry i j).add (hrowEntry i j)
  have hrightInt : Integrable (fun a : CoeffSpace d =>
      (∑ w ∈ Zp, ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)) +
      (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
      (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
        (3 : ℝ) ^ (jStar - (n + l)) * Y a) • toFullBlockMat E) P := by
    change Integrable (Fp + Fr + FG) P
    refine integrable_of_entries fun i j => ?_
    have heq : (fun a => (Fp + Fr + FG) a i j) =
        fun a => Fp a i j + Fr a i j + FG a i j := by
      funext a
      rw [Pi.add_apply, Pi.add_apply, Matrix.add_apply, Matrix.add_apply]
    rw [heq]
    exact ((hpackEntry i j).add (hrowEntry i j)).add (hGEntry i j)
  have hint := integral_mono' (integrable_toFullBlockMat hWint) hrightInt hraw
  rw [← toFullBlockMat_annealedBlock hWint] at hint
  change toFullBlockMat (annealedBlock P W) ≤
    ∫ a, (Fp a + Fr a) + FG a ∂P at hint
  have houter : (∫ a, (Fp a + Fr a) + FG a ∂P) =
      (∫ a, Fp a + Fr a ∂P) + ∫ a, FG a ∂P := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, entry_integral hrightInt i j, entry_integral hsumI i j,
      entry_integral hGI i j]
    have heq : (fun a => ((Fp a + Fr a) + FG a) i j) = fun a => (Fp a + Fr a) i j + FG a i j :=
      funext fun a => by rw [Matrix.add_apply]
    have hpr : Integrable (fun a => (Fp a + Fr a) i j) P := by
      have heq2 : (fun a => (Fp a + Fr a) i j) = fun a => Fp a i j + Fr a i j :=
        funext fun a => by rw [Matrix.add_apply]
      rw [heq2]
      exact (hpackEntry i j).add (hrowEntry i j)
    rw [heq, integral_add hpr (hGEntry i j)]
  have hinner : (∫ a, Fp a + Fr a ∂P) =
      (∫ a, Fp a ∂P) + ∫ a, Fr a ∂P := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, entry_integral hsumI i j, entry_integral hpackI i j,
      entry_integral hrowI i j]
    have heq : (fun a => (Fp a + Fr a) i j) = fun a => Fp a i j + Fr a i j :=
      funext fun a => by rw [Matrix.add_apply]
    rw [heq, integral_add (hpackEntry i j) (hrowEntry i j)]
  rw [houter, hinner] at hint
  dsimp only [Fp, Fr, FG] at hint
  have hpackSum :
      (∫ a, ∑ w ∈ Zp,
        ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) ∂P) =
        ∑ w ∈ Zp, ∫ a,
          ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) ∂P := by
    apply Matrix.ext
    intro i j
    rw [Matrix.sum_apply, entry_integral hpackI i j]
    have heqL : (fun a => Fp a i j) = fun a => ∑ w ∈ Zp,
        (((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)) i j := by
      funext a; dsimp only [Fp]; rw [Matrix.sum_apply]
    rw [heqL,
      integral_finsetSum Zp fun w hw =>
        hscaledEntry ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal)
          (adaptedCellAt q' n w) (hpackint w hw) i j]
    exact Finset.sum_congr rfl fun w hw =>
      (entry_integral (hscaled _ _ (hpackint w hw)) i j).symm
  have hrowSum :
      (∫ a, ∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P) =
        ∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r, ∫ a,
          ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P := by
    apply Matrix.ext
    intro i j
    rw [Matrix.sum_apply, entry_integral hrowI i j]
    have heqL : (fun a => Fr a i j) = fun a =>
        ∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
          (((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) i j := by
      funext a
      dsimp only [Fr]
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun r _ => by rw [Matrix.sum_apply]
    rw [heqL,
      integral_finsetSum (Finset.Icc jStar n) fun r hr =>
        integrable_finsetSum (Z r) fun w hw =>
          hscaledEntry ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal)
            (adaptedCellAt q r w) (hrowint r hr w hw) i j]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Matrix.sum_apply,
      integral_finsetSum (Z r) fun w hw =>
        hscaledEntry ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal)
          (adaptedCellAt q r w) (hrowint r hr w hw) i j]
    exact Finset.sum_congr rfl fun w hw =>
      (entry_integral (hscaled _ _ (hrowint r hr w hw)) i j).symm
  rw [hpackSum, hrowSum] at hint
  have hmeasp : HasMeasurableCoarseBlock P (adaptedCell q' n) :=
    Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq'pd n
  have hmeasq : ∀ r, HasMeasurableCoarseBlock P (adaptedCell q r) := fun r =>
    Recurrence.hasMeasurableCoarseBlock_adaptedCell P hqpd r
  have hpmean : ∀ w ∈ Zp,
      ∫ a, ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) ∂P =
        ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
          toFullBlockMat (adaptedMean P q' n) := by
    intro w hw
    have hbase : (∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) ∂P) =
        toFullBlockMat (adaptedMean P q' n) := by
      rw [← toFullBlockMat_annealedBlock (hpackint w hw),
        Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hq' hjn hmeasp w]
    apply Matrix.ext
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul,
      entry_integral (hscaled ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal)
        (adaptedCellAt q' n w) (hpackint w hw)) i j]
    have heqL : (fun a => (((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)) i j) =
        fun a => ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) *
          toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) i j :=
      funext fun a => by rw [Matrix.smul_apply, smul_eq_mul]
    rw [heqL, integral_const_mul,
      ← entry_integral (integrable_toFullBlockMat (hpackint w hw)) i j, hbase]
  have hrmean : ∀ r ∈ Finset.Icc jStar n, ∀ w ∈ Z r,
      ∫ a, ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P =
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (adaptedMean P q r) := by
    intro r hr w hw
    have hbase : (∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P) =
        toFullBlockMat (adaptedMean P q r) := by
      rw [← toFullBlockMat_annealedBlock (hrowint r hr w hw),
        Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hq
          (Finset.mem_Icc.mp hr).1 (hmeasq r) w]
    apply Matrix.ext
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul,
      entry_integral (hscaled ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal)
        (adaptedCellAt q r w) (hrowint r hr w hw)) i j]
    have heqL : (fun a => (((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) i j) =
        fun a => ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) *
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) i j :=
      funext fun a => by rw [Matrix.smul_apply, smul_eq_mul]
    rw [heqL, integral_const_mul,
      ← entry_integral (integrable_toFullBlockMat (hrowint r hr w hw)) i j, hbase]
  have hYE : (∫ a, (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
        (3 : ℝ) ^ (jStar - (n + l)) * Y a) • toFullBlockMat E ∂P) =
      (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
        (3 : ℝ) ^ (jStar - (n + l)) * (∫ a, Y a ∂P)) • toFullBlockMat E := by
    apply Matrix.ext
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, entry_integral hGI i j]
    have heqL : (fun a => FG a i j) = fun a =>
        (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
          (3 : ℝ) ^ (jStar - (n + l)) * Y a) * toFullBlockMat E i j := by
      funext a; dsimp only [FG]; rw [Matrix.smul_apply, smul_eq_mul]
    rw [heqL, integral_mul_const, integral_const_mul]
  rw [Finset.sum_congr rfl hpmean,
    Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl (hrmean r hr), hYE] at hint
  have hfactor :
      (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (adaptedMean P q r)) =
        ∑ r ∈ Finset.Icc jStar n,
          (∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
              toFullBlockMat (adaptedMean P q r) := by
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.sum_smul]
  rw [hfactor] at hint
  simpa [q, q', W, Cg, adaptedMean] using hint

end

end Bridge
end HighContrast
end Homogenization
