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
  have hpackI : Integrable Fp P := by
    dsimp only [Fp]
    simpa only [Pi.smul_apply] using integrable_finset_sum Zp (fun w hw =>
      (integrable_toFullBlockMat (hpackint w hw)).smul
        ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal))
  have hrowI : Integrable Fr P := by
    dsimp only [Fr]
    simpa only [Pi.smul_apply] using
      integrable_finset_sum (Finset.Icc jStar n) (fun r hr =>
        integrable_finset_sum (Z r) fun w hw =>
          (integrable_toFullBlockMat (hrowint r hr w hw)).smul
            ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal))
  have hGI : Integrable FG P := by
    dsimp only [FG]
    exact (hYint.const_mul (3 * Cg * gridRatio q q' *
      boundaryConst Cd g mq * zetaG g *
        (3 : ℝ) ^ (jStar - (n + l)))).smul_const (toFullBlockMat E)
  have hsumI : Integrable (fun a => Fp a + Fr a) P := hpackI.add hrowI
  have hrightInt : Integrable (fun a : CoeffSpace d =>
      (∑ w ∈ Zp, ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)) +
      (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
      (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
        (3 : ℝ) ^ (jStar - (n + l)) * Y a) • toFullBlockMat E) P := by
    change Integrable (Fp + Fr + FG) P
    exact (hpackI.add hrowI).add hGI
  have hint := integral_mono' (integrable_toFullBlockMat hWint) hrightInt hraw
  rw [← toFullBlockMat_annealedBlock hWint] at hint
  change toFullBlockMat (annealedBlock P W) ≤
    ∫ a, (Fp a + Fr a) + FG a ∂P at hint
  have houter : (∫ a, (Fp a + Fr a) + FG a ∂P) =
      (∫ a, Fp a + Fr a ∂P) + ∫ a, FG a ∂P := integral_add hsumI hGI
  have hinner : (∫ a, Fp a + Fr a ∂P) =
      (∫ a, Fp a ∂P) + ∫ a, Fr a ∂P := integral_add hpackI hrowI
  rw [houter, hinner] at hint
  dsimp only [Fp, Fr, FG] at hint
  have hpackSum :
      (∫ a, ∑ w ∈ Zp,
        ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) ∂P) =
        ∑ w ∈ Zp, ∫ a,
          ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a) ∂P := by
    simpa only [Pi.smul_apply] using
      (integral_finset_sum Zp fun w hw =>
        (integrable_toFullBlockMat (hpackint w hw)).smul
          ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal))
  have hrowSum :
      (∫ a, ∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P) =
        ∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r, ∫ a,
          ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P := by
    calc
      _ = ∑ r ∈ Finset.Icc jStar n, ∫ a, ∑ w ∈ Z r,
          ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
            toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P := by
        simpa only [Pi.smul_apply] using
          (integral_finset_sum (Finset.Icc jStar n) fun r hr =>
            integrable_finset_sum (Z r) fun w hw =>
              (integrable_toFullBlockMat (hrowint r hr w hw)).smul
                ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal))
      _ = _ := Finset.sum_congr rfl fun r hr => by
        simpa only [Pi.smul_apply] using
          (integral_finset_sum (Z r) fun w hw =>
            (integrable_toFullBlockMat (hrowint r hr w hw)).smul
              ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal))
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
    rw [integral_smul, ← toFullBlockMat_annealedBlock (hpackint w hw),
      Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hq' hjn hmeasp w]
  have hrmean : ∀ r ∈ Finset.Icc jStar n, ∀ w ∈ Z r,
      ∫ a, ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) ∂P =
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (adaptedMean P q r) := by
    intro r hr w hw
    rw [integral_smul, ← toFullBlockMat_annealedBlock (hrowint r hr w hw),
      Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hq
        (Finset.mem_Icc.mp hr).1 (hmeasq r) w]
  rw [Finset.sum_congr rfl hpmean,
    Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl (hrmean r hr),
    integral_smul_const, integral_const_mul] at hint
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
