/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CellMajorantAt
import HCPoly.Provider.Transport.CellGap
import HCPoly.Provider.Transport.RowDischarge

/-!
# The gap of an arbitrary target-cell majorant

The full maximal filling supplied by `Transport.exists_cell_majorant_at` also gives
the convex bundle needed by `Transport.cell_gap`.  This file records that bundle
without replacing the raw random majorant used by the collective absorption.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The gap of a full filling consists of its top-scale gain, its lower
boundary gains, the bridge error, and the normalized source residual. -/
theorem full_filling_gap_le (hd : 1 ≤ d) {Q g : ℝ} (hQ : 1 ≤ Q) {jStar j : ℤ}
    {theta : ℤ → ℝ} {Pold : ℤ → BlockMat d}
    {Pbar Mblk Phat KW Rm : BlockMat d} {S : FullBlockMat d}
    {eta eps Cb : ℝ}
    (hjj : jStar ≤ j)
    (hth : ∀ r ∈ Finset.Icc jStar j, 0 ≤ theta r)
    (hm : ∑ r ∈ Finset.Icc jStar j, theta r ≤ 1)
    (hbdry : ∀ r ∈ Finset.Ico jStar j,
      theta r ≤ Cb *
        (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))))
    (hPold : ∀ r ∈ Finset.Icc jStar j,
      (1 : FullBlockMat d) ≤ toFullBlockMat (Pold r))
    (hPbar : toFullBlockMat Pbar =
      ∑ r ∈ Finset.Icc jStar j, theta r • toFullBlockMat (Pold r) +
        (1 - ∑ r ∈ Finset.Icc jStar j, theta r) •
          (1 : FullBlockMat d))
    (heta : 0 ≤ eta) (heta3 : eta ≤ 1 / 3) (heps : 0 ≤ eps)
    (hS : Sᵀ * S ≤ (1 + eta) • (1 : FullBlockMat d))
    (hR : toFullBlockMat Rm ≤ eps • (1 : FullBlockMat d))
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk))
    (hKW : toFullBlockMat KW =
      Sᵀ * toFullBlockMat Pbar * S -
        (1 - ∑ r ∈ Finset.Icc jStar j, theta r) • (Sᵀ * S) +
        toFullBlockMat Rm)
    (hIK : (1 : FullBlockMat d) ≤ toFullBlockMat KW) :
    gapG Q KW ≤ 2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q *
      (frakH Q (Pold j) +
        Cb * ∑ r ∈ Finset.Ico jStar j,
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
            frakH Q (Pold r) +
        3 * eta + (eps + eps ^ Q)) := by
  classical
  have hQ0 : 0 ≤ Q := by linarith only [hQ]
  have hjmem : j ∈ Finset.Icc jStar j := Finset.mem_Icc.mpr ⟨hjj, le_rfl⟩
  have hnotmem : j ∉ Finset.Ico jStar j := by
    simp only [Finset.mem_Ico]
    omega
  have hins : insert j (Finset.Ico jStar j) = Finset.Icc jStar j :=
    Finset.Ico_insert_right hjj
  have hsub : Finset.Ico jStar j ⊆ Finset.Icc jStar j := by
    rw [← hins]
    exact Finset.subset_insert _ _
  have htop : theta j ≤ 1 :=
    (Finset.single_le_sum hth hjmem).trans hm
  have hgain0 : ∀ r ∈ Finset.Icc jStar j, 0 ≤ frakH Q (Pold r) := fun r hr =>
    zero_le_frakH hQ0 (hPold r hr)
  have hweights :
      ∑ r ∈ Finset.Icc jStar j, theta r * frakH Q (Pold r) ≤
        frakH Q (Pold j) +
          Cb * ∑ r ∈ Finset.Ico jStar j,
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
              frakH Q (Pold r) := by
    rw [← hins, Finset.sum_insert hnotmem]
    refine add_le_add ?_ ?_
    · simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right htop (hgain0 j hjmem))
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun r hr => by
        have h := mul_le_mul_of_nonneg_right (hbdry r hr)
          (hgain0 r (hsub hr))
        calc
          theta r * frakH Q (Pold r) ≤
              (Cb * (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ)))) *
                frakH Q (Pold r) := h
          _ = Cb * ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
                frakH Q (Pold r)) := by ring
  have hgap := cell_gap (Finset.Icc jStar j) hd hQ hth hm
    hPold hPbar heta heta3 heps hS hR hM hPhat hKW hIK
  have hcoef0 : 0 ≤ 2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q := by
    positivity
  exact hgap.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hweights le_rfl) le_rfl) hcoef0)

private theorem normalized_majorant_mean_eq
    {P : Measure (CoeffSpace d)} {q q' : Mat d} {jStar j t n : ℤ}
    {Z : ℤ → Finset (Fin d → ℤ)} {c : ℤ → ℝ}
    {E KG Pbar KW Rm : BlockMat d} {cb : ℝ}
    (hEt : (toFullBlockMat (adaptedMean P q t)).PosDef)
    (hF0 : (toFullBlockMat (adaptedMean P q' n)).PosDef)
    (hKG : toFullBlockMat KG =
      (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
          toFullBlockMat (adaptedMean P q r)) + cb • toFullBlockMat E)
    (hPbar : toFullBlockMat Pbar =
      ∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
          toFullBlockMat (relMean P q r t) +
        (1 - ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) •
          (1 : FullBlockMat d))
    (hRm : toFullBlockMat Rm =
      matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
        (cb • toFullBlockMat E) *
        matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹))
    (hKW : toFullBlockMat KW =
      (bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ *
          toFullBlockMat Pbar *
          bridgeMap (adaptedMean P q t) (adaptedMean P q' n) -
        (1 - ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) •
          ((bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ *
            bridgeMap (adaptedMean P q t) (adaptedMean P q' n)) +
        toFullBlockMat Rm) :
    normalizedBlock KG (adaptedMean P q' n) = KW := by
  apply toFullBlockMat_injective
  rw [Recurrence.toFullBlockMat_normalizedBlock, hKG, Matrix.mul_add,
    Matrix.add_mul, hKW, hPbar, hRm, matSqrt_inv hF0]
  have hbridge : ∀ r : ℤ,
      (bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ *
          toFullBlockMat (relMean P q r t) *
          bridgeMap (adaptedMean P q t) (adaptedMean P q' n) =
        matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
          toFullBlockMat (adaptedMean P q r) *
          matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) := fun r =>
    bridgeMap_conj_relMean hEt hF0
  have hsumbridge :
      (bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ *
          (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
            toFullBlockMat (relMean P q r t)) *
          bridgeMap (adaptedMean P q t) (adaptedMean P q' n) =
        ∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
          (matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
            toFullBlockMat (adaptedMean P q r) *
            matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul, hbridge r]
  have hnormsum :
      (matSqrt (toFullBlockMat (adaptedMean P q' n)))⁻¹ *
          (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
            toFullBlockMat (adaptedMean P q r)) *
          (matSqrt (toFullBlockMat (adaptedMean P q' n)))⁻¹ =
        ∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
          ((matSqrt (toFullBlockMat (adaptedMean P q' n)))⁻¹ *
            toFullBlockMat (adaptedMean P q r) *
            (matSqrt (toFullBlockMat (adaptedMean P q' n)))⁻¹) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_add, Matrix.add_mul, hsumbridge, hnormsum,
    matSqrt_inv hF0]
  noncomm_ring

/-- The arbitrary translated target-cell majorant, together with the direct
gap row of its normalized mean.  The filling runs through the target scale, so
its bulk gain is unshifted and every lower row has the boundary kernel. -/
theorem exists_cell_majorant_gap_at [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hd : 1 ≤ d) (hCd : 0 < Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu mu' : Mat d} (hmu : mu.PosDef) (hmu' : mu'.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar mu))
    (hq' : IsRoundedGrid jStar (roundedGrid jStar mu'))
    {Khop : ℝ}
    (hK : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop)
    {t n j : ℤ} (hjn : jStar ≤ n) (hjj : jStar ≤ j) (z : Fin d → ℤ)
    (hcontn : adaptedCell (roundedGrid jStar mu') n ⊆ centeredCube d M)
    (hcontj : adaptedCellAt (roundedGrid jStar mu') j z ⊆ centeredCube d M)
    {Q eta : ℝ} (hQ : 1 ≤ Q) (heta0 : 0 ≤ eta) (heta3 : eta ≤ 1 / 3)
    (hEt : (toFullBlockMat
      (adaptedMean P (roundedGrid jStar mu) t)).PosDef)
    (hF0 : (toFullBlockMat
      (adaptedMean P (roundedGrid jStar mu') n)).PosDef)
    (hS : (bridgeMap (adaptedMean P (roundedGrid jStar mu) t)
          (adaptedMean P (roundedGrid jStar mu') n))ᵀ *
        bridgeMap (adaptedMean P (roundedGrid jStar mu) t)
          (adaptedMean P (roundedGrid jStar mu') n) ≤
      (1 + eta) • (1 : FullBlockMat d))
    (hPold : ∀ r ∈ Finset.Icc jStar j,
      (1 : FullBlockMat d) ≤
        toFullBlockMat (relMean P (roundedGrid jStar mu) r t))
    (hPnew : (1 : FullBlockMat d) ≤
      toFullBlockMat (relMean P (roundedGrid jStar mu') j n)) :
    ∃ (Z : ℤ → Finset (Fin d → ℤ)) (c : ℤ → ℝ)
      (Gm : CoeffSpace d → BlockMat d) (KG : BlockMat d),
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
          6 * (d : ℝ) * Real.sqrt d * Khop *
            (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) ∧
      (∀ a, toFullBlockMat
          (coarseBlock (adaptedCellAt (roundedGrid jStar mu') j z) a) ≤
        toFullBlockMat (Gm a)) ∧
      (∀ a, IsSymmetricBlockMat (Gm a)) ∧
      (∀ α β : BlockCoord d,
        AEStronglyMeasurable (fun a => toFullBlockMat (Gm a) α β) P) ∧
      Integrable (fun a => toFullBlockMat (Gm a)) P ∧
      ((∫ a, toFullBlockMat (Gm a) ∂P) = toFullBlockMat KG) ∧
      IsSymmetricBlockMat KG ∧
      (toFullBlockMat KG =
        (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
            toFullBlockMat (adaptedMean P (roundedGrid jStar mu) r)) +
          (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu *
            zetaG g * (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P) •
              toFullBlockMat E) ∧
      (∀ᵐ a ∂P, toFullBlockMat (blockSub (Gm a) KG) =
        (∑ r ∈ Finset.Icc jStar j, ∑ w ∈ Z r, c r •
            toFullBlockMat (blockSub
              (coarseBlock (adaptedCellAt (roundedGrid jStar mu) r w) a)
              (adaptedMean P (roundedGrid jStar mu) r))) +
          (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu *
            zetaG g * (3 : ℝ) ^ (jStar - j) *
              (Y a - ∫ x, Y x ∂P)) • toFullBlockMat E) ∧
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu') j) ≤
        toFullBlockMat KG) ∧
      gapG Q (normalizedBlock KG
          (adaptedMean P (roundedGrid jStar mu') n)) ≤
        2 * 2 ^ Q * (1 + 2 * (d : ℝ)) ^ Q *
          (frakH Q (relMean P (roundedGrid jStar mu) j t) +
            (6 * (d : ℝ) * Real.sqrt d * Khop) *
              ∑ r ∈ Finset.Ico jStar j,
                (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
                  frakH Q (relMean P (roundedGrid jStar mu) r t) +
            3 * eta +
              ((6 * (d : ℝ) * Real.sqrt d * Khop *
                    boundaryConst Cd g mu * zetaG g *
                    (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P) *
                  (kappaRef E *
                    (boundaryConst Cd g mu' * ∫ a, Y a ∂P)) +
                ((6 * (d : ℝ) * Real.sqrt d * Khop *
                      boundaryConst Cd g mu * zetaG g *
                      (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P) *
                    (kappaRef E *
                      (boundaryConst Cd g mu' * ∫ a, Y a ∂P))) ^ Q)) := by
  classical
  obtain ⟨Z, c, Gm, KG, hZ, hZsub, hc, hcratio, hmass, hrow,
      hdom, hGsym, hGmeas, hGint, hGmean, hKGsym, hKG, hcentered, hmean⟩ :=
    exists_cell_majorant_at (P := P) (g := g) (E := E) (Ψ := Ψ)
      (K := K) (Cd := Cd) (Y := Y) (mu := mu) (mu' := mu')
      (Khop := Khop) hd hCd.le hg1 hE hEpd hP hY hmu hmu' hq hq'
      hK hjj z hcontj
  refine ⟨Z, c, Gm, KG, hZ, hZsub, hc, hcratio, hmass, hrow,
    hdom, hGsym, hGmeas, hGint, hGmean, hKGsym, hKG, hcentered, hmean, ?_⟩
  set q : Mat d := roundedGrid jStar mu
  set q' : Mat d := roundedGrid jStar mu'
  set cb : ℝ := 6 * (d : ℝ) * Real.sqrt d * Khop *
    boundaryConst Cd g mu * zetaG g * (3 : ℝ) ^ (jStar - j) *
      ∫ a, Y a ∂P
  set eps : ℝ := cb *
    (kappaRef E * (boundaryConst Cd g mu' * ∫ a, Y a ∂P))
  set S : FullBlockMat d := bridgeMap (adaptedMean P q t) (adaptedMean P q' n)
  set Pbar : BlockMat d := ofFullBlockMat
    (∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
        toFullBlockMat (relMean P q r t) +
      (1 - ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) •
        (1 : FullBlockMat d))
  set Rm : BlockMat d := ofFullBlockMat
    (matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
      (cb • toFullBlockMat E) *
      matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹))
  set Mblk : BlockMat d := ofFullBlockMat (Sᵀ * toFullBlockMat Pbar * S - 1)
  set Phat : BlockMat d := ofFullBlockMat
    (1 + toFullBlockMat (blockPosPart Mblk))
  set KW : BlockMat d := ofFullBlockMat
    (Sᵀ * toFullBlockMat Pbar * S -
      (1 - ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) • (Sᵀ * S) +
      toFullBlockMat Rm)
  have hPbarEq : toFullBlockMat Pbar =
      ∑ r ∈ Finset.Icc jStar j, (∑ _w ∈ Z r, c r) •
          toFullBlockMat (relMean P q r t) +
        (1 - ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) •
          (1 : FullBlockMat d) := toFullBlockMat_ofFullBlockMat _
  have hRmEq : toFullBlockMat Rm =
      matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
        (cb • toFullBlockMat E) *
        matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) :=
    toFullBlockMat_ofFullBlockMat _
  have hMEq : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1 :=
    toFullBlockMat_ofFullBlockMat _
  have hPhatEq : toFullBlockMat Phat =
      1 + toFullBlockMat (blockPosPart Mblk) :=
    toFullBlockMat_ofFullBlockMat _
  have hKWEq : toFullBlockMat KW =
      Sᵀ * toFullBlockMat Pbar * S -
        (1 - ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r) • (Sᵀ * S) +
        toFullBlockMat Rm := toFullBlockMat_ofFullBlockMat _
  have hcb0 : 0 ≤ cb := by
    have hKh : 0 ≤ Khop :=
      le_trans (le_trans zero_le_one (one_le_gridRatio q q')) hK
    have hYint : 0 ≤ ∫ a, Y a ∂P :=
      le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
    have h0 : 0 ≤ 6 * (d : ℝ) * Real.sqrt d * Khop := by positivity
    have h1 := mul_nonneg h0 (zero_le_boundaryConst hCd.le hg1 mu)
    have h2 := mul_nonneg h1 (zero_lt_zetaG hg1).le
    have h3 : 0 ≤ 6 * (d : ℝ) * Real.sqrt d * Khop *
        boundaryConst Cd g mu * zetaG g * (3 : ℝ) ^ (jStar - j) :=
      mul_nonneg h2 (zpow_nonneg (by norm_num) (jStar - j))
    exact mul_nonneg h3 hYint
  have heps0 : 0 ≤ eps := by
    change 0 ≤ cb *
      (kappaRef E * (boundaryConst Cd g mu' * ∫ a, Y a ∂P))
    exact mul_nonneg hcb0 (mul_nonneg (by
      rw [kappaRef, blockSize]
      exact Real.sInf_nonneg fun _ hx => hx.1)
      (mul_nonneg (zero_le_boundaryConst hCd.le hg1 mu')
        (le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY))))
  have hR : toFullBlockMat Rm ≤ eps • (1 : FullBlockMat d) := by
    exact toFullBlockMat_le_srcRow_smul_one hCd hg1 hE hEpd hY hmu' hq'
      hjn hcontn hcb0 hRmEq
  have hKGeq : normalizedBlock KG (adaptedMean P q' n) = KW := by
    apply normalized_majorant_mean_eq hEt hF0
    · simpa only [q, q', cb] using hKG
    · exact hPbarEq
    · exact hRmEq
    · exact hKWEq
  have hHK : toFullBlockMat (relMean P q' j n) ≤ toFullBlockMat KW := by
    rw [← hKGeq, Recurrence.toFullBlockMat_normalizedBlock,
      Recurrence.toFullBlockMat_relMean]
    exact conj_le_conj' (C := matSqrt (toFullBlockMat (adaptedMean P q' n))⁻¹)
      (by
        rw [conjTranspose_eq_transpose']
        exact transpose_matSqrt_inv hF0) hmean
  have hIK : (1 : FullBlockMat d) ≤ toFullBlockMat KW := hPnew.trans hHK
  have hth : ∀ r ∈ Finset.Icc jStar j, 0 ≤ ∑ _w ∈ Z r, c r := by
    intro r hr
    exact Finset.sum_nonneg fun _ _ => hc r
  have hCb0 : 0 ≤ 6 * (d : ℝ) * Real.sqrt d * Khop := by
    have hKh : 0 ≤ Khop :=
      le_trans (le_trans zero_le_one (one_le_gridRatio q q')) hK
    positivity
  have hbdry : ∀ r ∈ Finset.Ico jStar j,
      (∑ _w ∈ Z r, c r) ≤
        (6 * (d : ℝ) * Real.sqrt d * Khop) *
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) := by
    intro r hr
    have hrj : r < j := (Finset.mem_Ico.mp hr).2
    have hsharp := hrow r (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Ico.mp hr).1, hrj.le⟩) hrj
    have hrjR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hrj.le
    have hexp : (r : ℝ) - (j : ℝ) ≤
        -(1 - g) * ((j : ℝ) - (r : ℝ)) := by
      nlinarith only [hg0, hrjR]
    have hrate := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    exact hsharp.trans (mul_le_mul_of_nonneg_left hrate hCb0)
  have hgap := full_filling_gap_le (g := g) hd hQ hjj hth hmass hbdry
    (by simpa only [q] using hPold) hPbarEq heta0 heta3 heps0
    (by simpa only [S, q, q'] using hS) hR hMEq hPhatEq hKWEq hIK
  rw [← hKGeq] at hgap
  simpa only [q, q', cb, eps] using hgap

end

end Transport
end HighContrast
end Homogenization
