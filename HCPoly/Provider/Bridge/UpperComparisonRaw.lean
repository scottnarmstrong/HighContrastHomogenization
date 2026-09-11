/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.UpperWeightedRows
import HCPoly.Provider.Bridge.BridgeNormalization
import HCPoly.Provider.Transport.WindowDefinedness

/-!
# Raw upper two-grid comparison

A maximal filling of a new-grid cell by old-grid cells gives an undecayed
endpoint, a geometrically decaying boundary row, and the continued source row.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- The upper maximal filling, before its dimensional coefficients and source
row are absorbed into the common bridge constant. -/
theorem upper_comparison_raw [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    {n l : ℤ} (hl : 0 ≤ l) (hjn : jStar ≤ n - l)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ j : ℤ, jStar ≤ j → j ≤ n + l →
        adaptedCell r j ⊆ centeredCube d M) :
    toFullBlockMat (adaptedMean P (roundedGrid jStar mv) n) ≤
      toFullBlockMat (adaptedMean P (roundedGrid jStar mp) (n - l)) +
        ((1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
            (6 * (d : ℝ) * Real.sqrt d) *
            gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
            ((3 : ℝ) ^ (-(l : ℝ)) +
              (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
                linearDrift P rho (roundedGrid jStar mp) jStar n) +
          18 * (d : ℝ) * Real.sqrt d *
            bridgeContCoeff Cd g E jStar mp mv mp *
              (3 : ℝ) ^ (-(1 - g) * ((n : ℝ) - (jStar : ℝ)))) •
            toFullBlockMat (adaptedMean P (roundedGrid jStar mp) n) := by
  classical
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hqv := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmv
  have hqppd : qp.PosDef := Recurrence.posDef_of_isRoundedGrid hqp
  have hqvpd : qv.PosDef := Recurrence.posDef_of_isRoundedGrid hqv
  have hjn0 : jStar ≤ n := by omega
  have hnnl : n ≤ n + l := by omega
  have hdef := Transport.definedness_of_isWindowMultiplier hd hstat hE hQ hw hY
    hmp hmv (b := n + l) hcont
  have hfinp : ∀ j : ℤ, jStar ≤ j → j ≤ n + l →
      HasFiniteAdaptedMean P qp j := by
    intro j hj hjb
    exact (hdef.1 qp (Or.inl rfl) j hj hjb).1
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ :=
    Transport.maximal_filling hqvpd hqppd (n - l) n (0 : Vec d)
  let theta : ℤ → ℝ := fun a => ∑ w ∈ Z a,
    (volume (adaptedCellAt qp a w)).toReal /
      (volume (adaptedCellTranslate qv n 0)).toReal
  let F : ℤ → FullBlockMat d := fun a =>
    toFullBlockMat (adaptedMean P qp a)
  have hzero : adaptedCellTranslate qv n 0 = adaptedCell qv n := by
    simp [adaptedCellTranslate]
  have hselected : ∀ a : ℤ, ∀ w ∈ Z a,
      adaptedCellAt qp a w ⊆ centeredCube d M := by
    intro a w hw
    have hw' : w ∈ Transport.fillingIndex qp (n - l)
        (adaptedCellTranslate qv n 0) a := by
      rw [← hZ a]
      exact Finset.mem_coe.mpr hw
    exact (Transport.adaptedCellAt_subset_of_mem_fillingIndex hw').trans <| by
      rw [hzero]
      exact hcont qv (Or.inr rfl) n hjn0 hnnl
  have hZat : ∀ r, ↑(Z r) = Transport.fillingIndex qp (n - l)
      (adaptedCellAt qv n 0) r := by
    intro r
    rw [PortableHistory.adaptedCellAt_zero, ← hzero]
    exact hZ r
  have hraw := Transport.adaptedMean_le_filling_rows (P := P) (g := g) (E := E)
    (Ψ := Ψ) (K := K) (Cd := Cd) (Y := Y) (Khop := gridRatio qp qv)
    (n := n - l) (j := n) (z := 0) (Z := Z) (by omega : 1 ≤ d)
    (le_trans zero_le_one hCd) hg1 hE hEpd hstat hY hmp hmv hqp hqv le_rfl
    hjn hjn0 hZat (fun r w hw => hselected r w hw) (by
      rw [PortableHistory.adaptedCellAt_zero]
      exact hcont qv (Or.inr rfl) n hjn0 hnnl)
  have hraw' : toFullBlockMat (adaptedMean P qv n) ≤
      (∑ r ∈ Finset.Icc jStar (n - l), theta r • F r) +
        (6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv *
          boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - n) *
            ∫ a, Y a ∂P) • toFullBlockMat E := by
    simpa only [qp, qv, theta, F, PortableHistory.adaptedCellAt_zero, hzero] using hraw
  have hpos : ∀ r ∈ Finset.Icc jStar n, (F r).PosDef := by
    intro r hr
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hqp r
      (hfinp r (Finset.mem_Icc.mp hr).1 ((Finset.mem_Icc.mp hr).2.trans hnnl))
  have hmono : ∀ r ∈ Finset.Icc (jStar + 1) n, F r ≤ F (r - 1) := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    have hjrm : jStar ≤ r - 1 := by omega
    have hrn : r ≤ n := hrange.2
    have hrmTop : r - 1 ≤ n + l := by omega
    have hrTop : r ≤ n + l := hrn.trans hnnl
    exact Recurrence.toFullBlockMat_adaptedMean_le hstat hqp hjrm (by omega)
      (hfinp (r - 1) hjrm hrmTop) (hfinp r (by omega) hrTop)
  have hterminal : ∀ a ∈ Finset.Icc jStar (n - l - 1), F n ≤ F a := by
    intro a ha
    have harange := Finset.mem_Icc.mp ha
    have haTop : a ≤ n + l := by omega
    exact Recurrence.toFullBlockMat_adaptedMean_le hstat hqp
      harange.1 (by omega) (hfinp a harange.1 haTop) (hfinp n hjn0 hnnl)
  have htheta0 : ∀ a ∈ Finset.Icc jStar (n - l), 0 ≤ theta a := by
    intro a _
    exact Finset.sum_nonneg fun w _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hmass : ∑ a ∈ Finset.Icc jStar (n - l), theta a ≤ 1 := by
    dsimp only [theta]
    exact Transport.sum_relative_volume_le_one hqvpd hqppd hZ
  have hrow : ∀ a ∈ Finset.Icc jStar (n - l - 1),
      theta a ≤ (6 * (d : ℝ) * Real.sqrt d) * gridRatio qp qv *
        (3 : ℝ) ^ (a - n) := by
    intro a ha
    have harange := Finset.mem_Icc.mp ha
    dsimp only [theta]
    exact Transport.sum_relative_volume_row_le_hop (by omega : 1 ≤ d) hqvpd hqppd
      (by omega) (hZ a) le_rfl
  have hDK : 0 ≤ (6 * (d : ℝ) * Real.sqrt d) * gridRatio qp qv := by
    rw [gridRatio]
    positivity
  have hrows := weighted_mean_row_with_endpoint_le hrho0 hrho1 hl hjn hDK
    F theta hpos hmono hterminal htheta0 hmass hrow
  have hsrc := below_start_mean_le_terminal hCd hg0 hg1 hE hEpd hQ hw hY
    (mp := mp) (mv := mv) (mr := mp) hmp hqp (j := n) (t := n) hjn0 hjn0
    (hcont qp (Or.inl rfl) n hjn0 hnnl)
  have hstep := hraw'.trans (add_le_add hrows hsrc)
  have hdrift :
      (∑ r ∈ Finset.Icc (jStar + 1) n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - (r : ℝ))) *
          Matrix.trace ((F n)⁻¹ * (F (r - 1) - F r))) =
        linearDrift P rho qp jStar n := by
    simp only [linearDrift, F, blockTrace, toFullBlockMat_ofFullBlockMat,
      Recurrence.toFullBlockMat_blockSub]
  dsimp only [theta, F] at hstep
  rw [hdrift] at hstep
  simpa only [qp, qv, add_assoc, add_smul] using hstep

end

end Bridge
end HighContrast
end Homogenization
