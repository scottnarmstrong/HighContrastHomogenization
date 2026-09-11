/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ComparisonMatrixRows
import HCPoly.Provider.Bridge.HybridAnnealedRows
import HCPoly.Provider.Bridge.BridgeNormalization
import HCPoly.Provider.Transport.HybridVolumeBudget
import HCPoly.Provider.Transport.WindowDefinedness

/-!
# Raw reverse two-grid comparison

The packed new-grid row and the maximal old-grid filling of its uncovered
strip give the reverse comparison before the common bridge constant is chosen.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- The reverse hybrid filling with the packed fraction and every dimensional
coefficient still visible. -/
theorem lower_comparison_raw [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    {Cg D0 D : ℝ}
    (hCgEq : Cg = 2 * (d : ℝ) * Real.sqrt d +
      (2 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ) * Real.sqrt d) * 2 *
        (1 + 6 * Real.sqrt d) ^ (d - 1))
    (hD0Eq : D0 = 2 * (d : ℝ) * Real.sqrt d)
    (hDEq : D = 3 * Cg + D0)
    {n l : ℤ} (hl : 0 ≤ l) (hjn : jStar ≤ n)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ j : ℤ, jStar ≤ j → j ≤ n + l →
        adaptedCell r j ⊆ centeredCube d M) :
    ∃ alpha : ℝ,
      1 - D0 *
          gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
            (3 : ℝ) ^ (-(l : ℤ)) ≤ alpha ∧
      alpha ≤ 1 ∧
      toFullBlockMat (adaptedMean P (roundedGrid jStar mp) (n + l)) ≤
        alpha • toFullBlockMat (adaptedMean P (roundedGrid jStar mv) n) +
          ((1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
              D *
              gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
              ((3 : ℝ) ^ (-(l : ℝ)) +
                (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
                  linearDrift P rho (roundedGrid jStar mp) jStar (n + l)) +
            18 * (d : ℝ) * Real.sqrt d * Cg *
              bridgeContCoeff Cd g E jStar mp mv mp *
                (3 : ℝ) ^ (-(1 - g) * (((n + l : ℤ) : ℝ) - (jStar : ℝ)))) •
            toFullBlockMat (adaptedMean P (roundedGrid jStar mp) (n + l)) := by
  classical
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let T : ℤ := n + l
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hqv := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmv
  have hqppd : qp.PosDef := Recurrence.posDef_of_isRoundedGrid hqp
  have hqvpd : qv.PosDef := Recurrence.posDef_of_isRoundedGrid hqv
  have hnT : n ≤ T := by dsimp only [T]; omega
  have hjT : jStar ≤ T := hjn.trans hnT
  have hdef := Transport.definedness_of_isWindowMultiplier hd hstat hE hQ hw hY
    hmp hmv (b := T) (by simpa only [T] using hcont)
  have hfinp : ∀ j : ℤ, jStar ≤ j → j ≤ T → HasFiniteAdaptedMean P qp j := by
    intro j hj hjb
    exact (hdef.1 qp (Or.inl rfl) j hj hjb).1
  let Zp : Finset (Fin d → ℤ) :=
    (Transport.finite_hybridPackingIndex (n := n) hqvpd
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hqppd T).isBoundedDomain).toFinset
  let Z : ℤ → Finset (Fin d → ℤ) := fun r =>
    (Transport.finite_hybridFillingIndex hqppd (q' := qv) (n := n) (l := l)
      (a := r) (0 : Vec d)).toFinset
  have hZp : ↑Zp = Transport.hybridPackingIndex qv n (adaptedCell qp T) := by
    dsimp only [Zp, T]
    rw [(Transport.finite_hybridPackingIndex (n := n) hqvpd
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hqppd (n + l)).isBoundedDomain).coe_toFinset]
  have hZ : ∀ r, ↑(Z r) = Transport.fillingIndex qp n
      (Transport.hybridStrip qv n (adaptedCell qp T)) r := by
    intro r
    dsimp only [Z, T]
    rw [(Transport.finite_hybridFillingIndex hqppd (q' := qv) (n := n) (l := l)
      (a := r) (0 : Vec d)).coe_toFinset]
    simp [adaptedCellTranslate]
  have hzero : adaptedCellTranslate qp T 0 = adaptedCell qp T := by
    simp [adaptedCellTranslate]
  have hZpTrans : ↑Zp = Transport.hybridPackingIndex qv n
      (adaptedCellTranslate qp (n + l) 0) := by
    simpa only [T, hzero] using hZp
  have hZTrans : ∀ r, ↑(Z r) = Transport.fillingIndex qp n
      (Transport.hybridStrip qv n (adaptedCellTranslate qp (n + l) 0)) r := by
    intro r
    simpa only [T, hzero] using hZ r
  let alpha : ℝ := ∑ w ∈ Zp,
    (volume (adaptedCellAt qv n w)).toReal / (volume (adaptedCell qp T)).toReal
  let theta : ℤ → ℝ := fun a => ∑ w ∈ Z a,
    (volume (adaptedCellAt qp a w)).toReal / (volume (adaptedCell qp T)).toReal
  let F : ℤ → FullBlockMat d := fun a => toFullBlockMat (adaptedMean P qp a)
  have hpack : 1 - D0 * gridRatio qp qv * (3 : ℝ) ^ (-(l : ℤ)) ≤ alpha := by
    dsimp only [alpha]
    simpa [hD0Eq, adaptedCellTranslate] using
      Transport.one_sub_le_sum_relative_volume_hybridPacking (by omega : 1 ≤ d)
        hqppd hqvpd (n := n) (l := l) (0 : Vec d) hZpTrans
  have hpackOne : alpha ≤ 1 := by
    dsimp only [alpha]
    have hrow := Transport.sum_relative_volume_row_le_one hqppd hqvpd (a := n)
      (show ↑Zp = Transport.fillingIndex qv n
        (adaptedCellTranslate qp (n + l) 0) n by
          simpa only [Transport.hybridPackingIndex] using hZpTrans)
    simpa only [T, hzero] using hrow
  have hraw := adaptedMean_le_hybrid_rows hd (le_trans zero_le_one hCd) hg1 hE hEpd
    hstat hY hmp hmv hqp hqv hjn
    (hcont qp (Or.inl rfl) T hjT (by dsimp only [T]; exact le_rfl)) Zp Z hZp hZ
  rw [← hCgEq] at hraw
  have hpos : ∀ r ∈ Finset.Icc jStar T, (F r).PosDef := by
    intro r hr
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hqp r
      (hfinp r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)
  have hmono : ∀ r ∈ Finset.Icc (jStar + 1) T, F r ≤ F (r - 1) := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    have hjrm : jStar ≤ r - 1 := by omega
    have hrmT : r - 1 ≤ T := by omega
    exact Recurrence.toFullBlockMat_adaptedMean_le hstat hqp hjrm (by omega)
      (hfinp (r - 1) hjrm hrmT) (hfinp r (by omega) hrange.2)
  have hterminal : ∀ a ∈ Finset.Icc jStar n, F T ≤ F a := by
    intro a ha
    have harange := Finset.mem_Icc.mp ha
    have haT : a ≤ T := harange.2.trans hnT
    exact Recurrence.toFullBlockMat_adaptedMean_le hstat hqp harange.1 haT
      (hfinp a harange.1 haT) (hfinp T hjT le_rfl)
  have htheta0 : ∀ a ∈ Finset.Icc jStar n, 0 ≤ theta a := by
    intro a _
    exact Finset.sum_nonneg fun w _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hmass : ∑ a ∈ Finset.Icc jStar n, theta a ≤
      D0 * gridRatio qp qv * (3 : ℝ) ^ (-(l : ℤ)) := by
    dsimp only [theta]
    simpa [hD0Eq, adaptedCellTranslate, T] using
      Transport.sum_relative_volume_hybridFilling_le_strip (by omega : 1 ≤ d)
        hqppd hqvpd (n := n) (l := l) (0 : Vec d) hZTrans
  have hCg0 : 0 ≤ Cg := by rw [hCgEq]; positivity
  have hD00 : 0 ≤ D0 := by rw [hD0Eq]; positivity
  have hD0D : D0 ≤ D := by rw [hDEq]; linarith only [hCg0]
  have h3CgD : 3 * Cg ≤ D := by rw [hDEq]; linarith only [hD00]
  have hgrid0 : 0 ≤ gridRatio qp qv := le_trans zero_le_one (Transport.one_le_gridRatio _ _)
  have hrow : ∀ a ∈ Finset.Icc jStar n,
      theta a ≤ D * gridRatio qp qv * (3 : ℝ) ^ (a - T) := by
    intro a ha
    have harange := Finset.mem_Icc.mp ha
    by_cases han : a < n
    · have hv := Transport.sum_relative_volume_hybridFilling_row_le hd hqppd hqvpd
          han (0 : Vec d) (hZTrans a)
      rw [← hCgEq] at hv
      rw [show n + l = T by rfl, hzero] at hv
      change theta a ≤ Cg * gridRatio qp qv * (3 : ℝ) ^ (a + 1 - T) at hv
      have hpow : (3 : ℝ) ^ (a + 1 - T) = 3 * (3 : ℝ) ^ (a - T) := by
        rw [show a + 1 - T = 1 + (a - T) by ring,
          zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
      rw [hpow] at hv
      calc
        theta a ≤ Cg * gridRatio qp qv * (3 * (3 : ℝ) ^ (a - T)) := hv
        _ = (3 * Cg) * gridRatio qp qv * (3 : ℝ) ^ (a - T) := by ring
        _ ≤ D * gridRatio qp qv * (3 : ℝ) ^ (a - T) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h3CgD hgrid0)
            (zpow_nonneg (by norm_num) _)
    · have hanEq : a = n := by omega
      subst a
      have hsingle := Finset.single_le_sum (f := theta) htheta0
        (Finset.mem_Icc.mpr ⟨hjn, le_rfl⟩)
      refine hsingle.trans (hmass.trans ?_)
      have hpow : (3 : ℝ) ^ (n - T) = (3 : ℝ) ^ (-(l : ℤ)) := by
        congr 1
        dsimp only [T]
        ring
      rw [hpow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hD0D hgrid0) (zpow_nonneg (by norm_num) _)
  have hDnonneg : 0 ≤ D := hD00.trans hD0D
  have hDK : 0 ≤ D * gridRatio qp qv := mul_nonneg hDnonneg hgrid0
  have hTsub : T - l = n := by dsimp only [T]; ring
  have hrows := weighted_mean_row_le hrho0 hrho1 hl (by rw [hTsub]; exact hjn) hDK
    F theta hpos hmono
    (fun a ha => hterminal a (by rw [hTsub] at ha; exact ha))
    (fun a ha => htheta0 a (by rw [hTsub] at ha; exact ha))
    (by simpa only [hTsub] using hmass)
    (fun a ha => hrow a (by rw [hTsub] at ha; exact ha))
  rw [hTsub] at hrows
  have hratio : (3 : ℝ) ^ (-(1 : ℝ)) < 1 :=
    PortableHistory.geom_ratio_lt_one (by norm_num)
  have hratio0 : 0 < (3 : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hG1 : 1 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))) := by
    rw [le_div_iff₀ (sub_pos.mpr hratio)]
    linarith only [hratio0]
  have hD0GD : D0 ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D := by
    exact hD0D.trans <| by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hG1 hDnonneg
  have hfirst : D0 * gridRatio qp qv * (3 : ℝ) ^ (-(l : ℤ)) ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * gridRatio qp qv *
        (3 : ℝ) ^ (-(l : ℤ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hD0GD hgrid0) (zpow_nonneg (by norm_num) _)
  have hpowCast : (3 : ℝ) ^ (-(l : ℤ)) = (3 : ℝ) ^ (-(l : ℝ)) := by
    symm
    simpa only [Int.cast_neg] using Real.rpow_intCast (3 : ℝ) (-l)
  have hcoefrow :
      D0 * gridRatio qp qv * (3 : ℝ) ^ (-(l : ℤ)) +
          (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * gridRatio qp qv *
            (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
              linearDrift P rho qp jStar T ≤
        (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * gridRatio qp qv *
          ((3 : ℝ) ^ (-(l : ℝ)) +
            (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
              linearDrift P rho qp jStar T) := by
    calc
      _ ≤ (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * gridRatio qp qv *
            (3 : ℝ) ^ (-(l : ℤ)) +
          (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * gridRatio qp qv *
            (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
              linearDrift P rho qp jStar T := add_le_add hfirst le_rfl
      _ = _ := by
        rw [hpowCast, mul_add]
        simp only [mul_assoc]
  have hFTps : (F T).PosSemidef := (hpos T
    (Finset.mem_Icc.mpr ⟨hjT, le_rfl⟩)).posSemidef
  have hbelow := below_start_mean_le_terminal hCd hg0 hg1 hE hEpd hQ hw hY
    (mp := mp) (mv := mv) (mr := mp) hmp hqp (j := T) (t := T) hjT hjT
    (hcont qp (Or.inl rfl) T hjT (by dsimp only [T]; exact le_rfl))
  have hEps : (toFullBlockMat E).PosSemidef :=
    (posDef_toFullBlockMat hE hEpd).posSemidef
  have hB0 : 0 ≤ boundaryConst Cd g mp :=
    Transport.zero_le_boundaryConst (le_trans zero_le_one hCd) hg1 mp
  have hzeta0 : 0 ≤ zetaG g := (Transport.zero_lt_zetaG hg1).le
  have hmean0 : 0 ≤ ∫ a, Y a ∂P :=
    le_trans zero_le_one (Transport.one_le_integral_of_isWindowMultiplier hY)
  have hcommon0 : 0 ≤ gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
      (3 : ℝ) ^ (jStar - T) * ∫ a, Y a ∂P := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hgrid0 hB0) hzeta0) (zpow_nonneg (by norm_num) _)) hmean0
  have hD0one : 1 ≤ D0 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hsqrt : 1 ≤ Real.sqrt d := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith only [hdR])
    rw [hD0Eq]
    nlinarith only [hdR, hsqrt]
  have hrawcoef : 3 * Cg *
      (gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
        (3 : ℝ) ^ (jStar - T) * ∫ a, Y a ∂P) ≤
      Cg * (6 * (d : ℝ) * Real.sqrt d *
        (gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
          (3 : ℝ) ^ (jStar - T) * ∫ a, Y a ∂P)) := by
    have hbase := mul_le_mul_of_nonneg_left hD0one hCg0
    have hmul := mul_le_mul_of_nonneg_right hbase
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hcommon0)
    calc
      3 * Cg *
          (gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
            (3 : ℝ) ^ (jStar - T) * ∫ a, Y a ∂P) =
        (Cg * 1) * (3 *
          (gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
            (3 : ℝ) ^ (jStar - T) * ∫ a, Y a ∂P)) := by ring
      _ ≤ (Cg * D0) * (3 *
          (gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
            (3 : ℝ) ^ (jStar - T) * ∫ a, Y a ∂P)) := hmul
      _ = Cg * (6 * (d : ℝ) * Real.sqrt d *
          (gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
            (3 : ℝ) ^ (jStar - T) * ∫ a, Y a ∂P)) := by
        rw [hD0Eq]
        ring
  have hrawcoef' :
      3 * Cg * gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
          (3 : ℝ) ^ (jStar - T) * (∫ a, Y a ∂P) ≤
        Cg * (6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv *
          boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - T) *
            (∫ a, Y a ∂P)) := by
    convert hrawcoef using 1 <;> ring
  have hsource0 :
      (3 * Cg * gridRatio qp qv * boundaryConst Cd g mp * zetaG g *
          (3 : ℝ) ^ (jStar - T) * (∫ a, Y a ∂P)) • toFullBlockMat E ≤
        Cg • ((6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv *
          boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - T) *
            (∫ a, Y a ∂P)) • toFullBlockMat E) := by
    rw [smul_smul]
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hEps.smul (sub_nonneg.mpr hrawcoef')
  have hsource := hsource0.trans (smul_le_smul_of_le hCg0 hbelow)
  have hdrift :
      (∑ r ∈ Finset.Icc (jStar + 1) T,
        (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
          Matrix.trace ((F T)⁻¹ * (F (r - 1) - F r))) =
        linearDrift P rho qp jStar T := by
    simp only [linearDrift, F, blockTrace, toFullBlockMat_ofFullBlockMat,
      Recurrence.toFullBlockMat_blockSub]
  rw [hdrift] at hrows
  have hrows' : ∑ a ∈ Finset.Icc jStar n, theta a • F a ≤
      ((1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * gridRatio qp qv *
        ((3 : ℝ) ^ (-(l : ℝ)) +
          (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
            linearDrift P rho qp jStar T)) • F T := by
    refine hrows.trans ?_
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hFTps.smul (sub_nonneg.mpr hcoefrow)
  refine ⟨alpha, hpack, hpackOne, ?_⟩
  have hstep := hraw.trans <| add_le_add (add_le_add le_rfl hrows') hsource
  dsimp only [alpha, theta, F] at hstep
  rw [← Finset.sum_smul] at hstep
  dsimp only [alpha]
  simpa only [qp, qv, T, add_assoc, add_smul, smul_smul,
    mul_assoc, mul_comm, mul_left_comm] using hstep

end

end Bridge
end HighContrast
end Homogenization
