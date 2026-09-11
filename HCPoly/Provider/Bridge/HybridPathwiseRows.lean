/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.HybridRowAlgebra
import HCPoly.Provider.Transport.AnnealedRows

/-!
# Pathwise reverse-hybrid rows

The hybrid packing and the maximal filling of its uncovered strip form a
finite matrix majorant at every environment where the window cell bounds hold.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- The reverse hybrid exhaustion as a pathwise matrix inequality.  The first
row is packed on the new grid, the finite selected rows remain on the old grid,
and all rows below the alignment scale are absorbed into the multiplier term. -/
theorem coarseBlock_le_hybrid_rows [NeZero d]
    (hd : 2 ≤ d) (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mq mq' : Mat d} (hmq : mq.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar mq))
    (hq' : IsRoundedGrid jStar (roundedGrid jStar mq'))
    {n l : ℤ} (hjn : jStar ≤ n)
    (hcont : adaptedCell (roundedGrid jStar mq) (n + l) ⊆ centeredCube d M)
    (Zp : Finset (Fin d → ℤ)) (Z : ℤ → Finset (Fin d → ℤ))
    (hZp : ↑Zp = Transport.hybridPackingIndex (roundedGrid jStar mq') n
      (adaptedCell (roundedGrid jStar mq) (n + l)))
    (hZ : ∀ r, ↑(Z r) = Transport.fillingIndex (roundedGrid jStar mq) n
      (Transport.hybridStrip (roundedGrid jStar mq') n
        (adaptedCell (roundedGrid jStar mq) (n + l))) r)
    (a : CoeffSpace d)
    (ha : ∀ nu : Mat d, nu.PosDef → ∀ r : ℤ, ∀ y : Vec d,
      adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M →
        BlockMatLoewnerLE
          (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
          (blockScale (boundaryConst Cd g nu * Y a * burnDiscount g jStar r) E)) :
    toFullBlockMat
        (coarseBlock (adaptedCell (roundedGrid jStar mq) (n + l)) a) ≤
      (∑ w ∈ Zp,
        ((volume (adaptedCellAt (roundedGrid jStar mq') n w)).toReal /
          (volume (adaptedCell (roundedGrid jStar mq) (n + l))).toReal) •
            toFullBlockMat
              (coarseBlock (adaptedCellAt (roundedGrid jStar mq') n w) a)) +
        (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
          ((volume (adaptedCellAt (roundedGrid jStar mq) r w)).toReal /
            (volume (adaptedCell (roundedGrid jStar mq) (n + l))).toReal) •
              toFullBlockMat
                (coarseBlock (adaptedCellAt (roundedGrid jStar mq) r w) a)) +
        (3 * (2 * (d : ℝ) * Real.sqrt d +
              (2 * (d : ℝ) * Real.sqrt d) *
                (2 * (d : ℝ) * Real.sqrt d) * 2 *
                  (1 + 6 * Real.sqrt d) ^ (d - 1)) *
            gridRatio (roundedGrid jStar mq) (roundedGrid jStar mq') *
            boundaryConst Cd g mq * zetaG g *
            (3 : ℝ) ^ (jStar - (n + l)) * Y a) • toFullBlockMat E := by
  classical
  let q := roundedGrid jStar mq
  let q' := roundedGrid jStar mq'
  let W := adaptedCell q (n + l)
  have hqpd : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hq'pd : q'.PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  have hzero : adaptedCellTranslate q (n + l) 0 = W := by
    simp [W, adaptedCellTranslate]
  have hcell : ∀ r, ∀ w ∈ Z r, adaptedCellAt q r w ⊆ centeredCube d M := by
    intro r w hw
    have hw' : w ∈ Transport.fillingIndex q n (Transport.hybridStrip q' n W) r := by
      rw [← hZ r]
      exact Finset.mem_coe.mpr hw
    exact (Transport.adaptedCellAt_subset_of_mem_fillingIndex hw').trans
      (Transport.hybridStrip_subset.trans hcont)
  let Cg : ℝ := 2 * (d : ℝ) * Real.sqrt d +
    (2 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ) * Real.sqrt d) * 2 *
      (1 + 6 * Real.sqrt d) ^ (d - 1)
  have hCg0 : 0 ≤ Cg := by dsimp only [Cg]; positivity
  have hgrid0 : 0 ≤ gridRatio q q' := by rw [gridRatio]; positivity
  have hB0 : 0 ≤ boundaryConst Cd g mq := Transport.zero_le_boundaryConst hCd hg mq
  have hzeta : 0 ≤ zetaG g := (Transport.zero_lt_zetaG hg).le
  have hEps : (toFullBlockMat E).PosSemidef :=
    (posDef_toFullBlockMat hE hEpd).posSemidef
  let c : ℝ := 3 * Cg * gridRatio q q' * boundaryConst Cd g mq * zetaG g *
    (3 : ℝ) ^ (jStar - (n + l)) * Y a
  let B : BlockMat d := ofFullBlockMat
    ((∑ w ∈ Zp, ((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)) +
      (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
      c • toFullBlockMat E)
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hCg0) hgrid0) hB0) hzeta) (by positivity))
      (le_trans zero_le_one (hY.one_le a))
  have hpackps : ∀ w ∈ Zp,
      (((volume (adaptedCellAt q' n w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q' n w) a)).PosSemidef := by
    intro w _
    exact (Transport.posSemidef_toFullBlockMat_coarseBlock
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq'pd n w)
      (Recurrence.volume_adaptedCellAt_pos hq'pd n w).ne' a).smul
        (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hrowps : ∀ r ∈ Finset.Icc jStar n, ∀ w ∈ Z r,
      (((volume (adaptedCellAt q r w)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)).PosSemidef := by
    intro r _ w _
    exact (Transport.posSemidef_toFullBlockMat_coarseBlock
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hqpd r w)
      (Recurrence.volume_adaptedCellAt_pos hqpd r w).ne' a).smul
        (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hBps : (toFullBlockMat B).PosSemidef := by
    rw [show toFullBlockMat B = _ by exact toFullBlockMat_ofFullBlockMat _]
    exact ((hybrid_posSemidef_finset_sum hpackps).add
      (hybrid_posSemidef_finset_sum fun r hr =>
        hybrid_posSemidef_finset_sum (hrowps r hr))).add (hEps.smul hc0)
  have hBsym : IsSymmetricBlockMat B := isSymmetricBlockMat_of_posSemidef hBps
  have hT : ∀ X : BlockVec d, ∀ J : ℤ, J ≤ n →
      (∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal / (volume W).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
      ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal / (volume W).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X)) ≤
        1 / 2 * blockVecDot X (blockMatVecMul B X) := by
    intro X J _
    let row : ℤ → ℝ := fun r => ∑ w ∈ Z r,
      (volume (adaptedCellAt q r w)).toReal / (volume W).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))
    have hrow0 : ∀ r, 0 ≤ row r := fun r => Finset.sum_nonneg fun w _ =>
      mul_nonneg (by positivity) (by
        have hp := Transport.posSemidef_toFullBlockMat_coarseBlock
          (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hqpd r w)
          (Recurrence.volume_adaptedCellAt_pos hqpd r w).ne' a
        have hx := hp.dotProduct_mulVec_nonneg (toFullBlockVec X)
        rw [blockVecDot_blockMatVecMul_eq_dotProduct]
        have hx' : 0 ≤ toFullBlockVec X ⬝ᵥ
            toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) *ᵥ
              toFullBlockVec X := by simpa using hx
        positivity)
    have hEq : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
      have hx := hEps.dotProduct_mulVec_nonneg (toFullBlockVec X)
      rw [blockVecDot_blockMatVecMul_eq_dotProduct]
      have hx' : 0 ≤ toFullBlockVec X ⬝ᵥ toFullBlockMat E *ᵥ
          toFullBlockVec X := by simpa using hx
      positivity
    have hbelow : ∀ J' : ℤ, ∑ r ∈ Finset.Ico J' jStar, row r ≤
        c * (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
      intro J'
      have hrows : ∀ r ∈ Finset.Ico J' jStar, row r ≤
          Cg * gridRatio q q' * (3 : ℝ) ^ (r + 1 - (n + l)) *
            (boundaryConst Cd g mq * Y a * burnDiscount g jStar r) *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
        intro r hr
        have hrn : r < n := lt_of_lt_of_le (Finset.mem_Ico.mp hr).2 hjn
        have hzrow : ↑(Z r) = Transport.fillingIndex q n
            (Transport.hybridStrip q' n (adaptedCellTranslate q (n + l) 0)) r := by
          simpa only [hzero] using hZ r
        have hvol := Transport.sum_relative_volume_hybridFilling_row_le
          hd hqpd hq'pd hrn 0 hzrow
        have hvol' : ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal / (volume W).toReal ≤
            Cg * gridRatio q q' * (3 : ℝ) ^ (r + 1 - (n + l)) := by
          simpa only [hzero, Cg] using hvol
        have hcellbd : ∀ w ∈ Z r,
            1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X) ≤
            (boundaryConst Cd g mq * Y a * burnDiscount g jStar r) *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
          intro w hw
          have hle := ha mq hmq r (adaptedCellCenter q r w) (hcell r w hw) X
          rw [Sharp.blockVecDot_blockMatVecMul_blockScale,
            ← Transport.adaptedCellAt_eq_adaptedCellTranslate] at hle
          linarith only [hle]
        calc
          row r ≤ ∑ w ∈ Z r,
              (volume (adaptedCellAt q r w)).toReal / (volume W).toReal *
                ((boundaryConst Cd g mq * Y a * burnDiscount g jStar r) *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X))) :=
            Finset.sum_le_sum fun w hw =>
              mul_le_mul_of_nonneg_left (hcellbd w hw) (by positivity)
          _ = (∑ w ∈ Z r,
              (volume (adaptedCellAt q r w)).toReal / (volume W).toReal) *
                ((boundaryConst Cd g mq * Y a * burnDiscount g jStar r) *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
            rw [Finset.sum_mul]
          _ ≤ (Cg * gridRatio q q' * (3 : ℝ) ^ (r + 1 - (n + l))) *
                ((boundaryConst Cd g mq * Y a * burnDiscount g jStar r) *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X))) :=
            mul_le_mul_of_nonneg_right hvol'
              (mul_nonneg (mul_nonneg (mul_nonneg hB0
                (le_trans zero_le_one (hY.one_le a)))
                (Transport.zero_lt_burnDiscount g jStar r).le) hEq)
          _ = _ := by ring
      refine (Finset.sum_le_sum hrows).trans ?_
      have hs := Transport.sum_belowStart_weight_le hg jStar (n + l) J'
      have hfac : 0 ≤ 3 * Cg * gridRatio q q' * boundaryConst Cd g mq * Y a *
          (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num) hCg0) hgrid0) hB0)
          (le_trans zero_le_one (hY.one_le a))) hEq
      have hpow : ∀ r : ℤ,
          (3 : ℝ) ^ (r + 1 - (n + l)) = 3 * (3 : ℝ) ^ (r - (n + l)) := by
        intro r
        rw [show r + 1 - (n + l) = 1 + (r - (n + l)) by ring,
          zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
      have hsum : ∑ r ∈ Finset.Ico J' jStar,
          Cg * gridRatio q q' * (3 : ℝ) ^ (r + 1 - (n + l)) *
            (boundaryConst Cd g mq * Y a * burnDiscount g jStar r) *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)) =
          (3 * Cg * gridRatio q q' * boundaryConst Cd g mq * Y a *
            (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
            ∑ r ∈ Finset.Ico J' jStar,
              (3 : ℝ) ^ (r - (n + l)) * burnDiscount g jStar r := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [hpow r]; ring
      rw [hsum]
      have hm := mul_le_mul_of_nonneg_left hs hfac
      dsimp only [c]
      convert hm using 1
      all_goals ring
    have hsel := hybrid_sum_Icc_le_add_of_below hjn hrow0
      (mul_nonneg hc0 hEq) hbelow J
    rw [show 1 / 2 * blockVecDot X (blockMatVecMul B X) =
        (∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal / (volume W).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
        (∑ r ∈ Finset.Icc jStar n, row r) +
        c * (1 / 2 * blockVecDot X (blockMatVecMul E X)) by
      exact blockQuadratic_hybridMajorant X Zp Z (Finset.Icc jStar n)
        _ _ _ _ c E]
    change
      (∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal / (volume W).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
          ∑ r ∈ Finset.Icc J n, row r ≤
        (∑ w ∈ Zp, (volume (adaptedCellAt q' n w)).toReal / (volume W).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
          (∑ r ∈ Finset.Icc jStar n, row r) +
            c * (1 / 2 * blockVecDot X (blockMatVecMul E X))
    calc
      _ = (∑ r ∈ Finset.Icc J n, row r) +
            (∑ w ∈ Zp,
              (volume (adaptedCellAt q' n w)).toReal / (volume W).toReal *
                (1 / 2 * blockVecDot X
                  (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) :=
        add_comm _ _
      _ ≤ ((∑ r ∈ Finset.Icc jStar n, row r) +
              c * (1 / 2 * blockVecDot X (blockMatVecMul E X))) +
            (∑ w ∈ Zp,
              (volume (adaptedCellAt q' n w)).toReal / (volume W).toReal *
                (1 / 2 * blockVecDot X
                  (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) :=
        add_le_add_left hsel _
      _ = (∑ w ∈ Zp,
            (volume (adaptedCellAt q' n w)).toReal / (volume W).toReal *
              (1 / 2 * blockVecDot X
                (blockMatVecMul (coarseBlock (adaptedCellAt q' n w) a) X))) +
            ((∑ r ∈ Finset.Icc jStar n, row r) +
              c * (1 / 2 * blockVecDot X (blockMatVecMul E X))) :=
        add_comm _ _
      _ = _ := by ring
  have hZp0 : ↑Zp = Transport.hybridPackingIndex q' n
      (adaptedCellTranslate q (n + l) 0) := by rw [hzero]; exact hZp
  have hZ0 : ∀ r, ↑(Z r) = Transport.fillingIndex q n
      (Transport.hybridStrip q' n (adaptedCellTranslate q (n + l) 0)) r := by
    intro r
    rw [hzero]
    exact hZ r
  have hle : toFullBlockMat (coarseBlock W a) ≤ toFullBlockMat B := by
    refine le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock W a) hBsym ?_
    intro X
    have hquad := Transport.blockQuadratic_coarseBlock_le_of_forall_hybrid_rows
      hd hqpd hq'pd (n := n) (l := l) 0 hZp0 hZ0
      a X (fun J hJ => by simpa only [hzero] using hT X J hJ)
    simpa only [hzero] using hquad
  rw [show toFullBlockMat B = _ by exact toFullBlockMat_ofFullBlockMat _] at hle
  simpa only [q, q', W, Cg] using hle

end

end Bridge
end HighContrast
end Homogenization
