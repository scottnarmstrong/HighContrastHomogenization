/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.BridgeNormalization
import HCPoly.Provider.Transport.RowDischarge
import HCPoly.Provider.Transport.WhitneyRows

/-!
# Filling rows for the shifted comparison

At a shifted target scale, the maximal filling is kept as an endpoint row,
explicit geometric earlier rows, and one continued row normalized by the fixed
terminal old-grid mean.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ}
  {Y : CoeffSpace d → ℝ}

/-- The continued-regime filling at scale `j`, with every old-grid boundary
row exposed and the below-alignment row normalized by the terminal scale `T`. -/
theorem shifted_fill_rows [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {j l T : ℤ} (hl : 0 ≤ l) (hjl : jStar ≤ j - l) (hjT : j ≤ T)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ a : ℤ, jStar ≤ a → a ≤ T →
        adaptedCell r a ⊆ centeredCube d M) :
    toFullBlockMat (adaptedMean P (roundedGrid jStar mv) j) ≤
      toFullBlockMat (adaptedMean P (roundedGrid jStar mp) (j - l)) +
        ∑ a ∈ Finset.Icc jStar (j - l - 1),
          (6 * (d : ℝ) * Real.sqrt d *
            gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
              (3 : ℝ) ^ (a - j)) •
            toFullBlockMat (adaptedMean P (roundedGrid jStar mp) a) +
        (18 * (d : ℝ) * Real.sqrt d *
          bridgeContCoeff Cd g E jStar mp mv mp *
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ)))) •
          toFullBlockMat (adaptedMean P (roundedGrid jStar mp) T) := by
  classical
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let U : ℤ := j - l
  have hjj : jStar ≤ j := by omega
  have hjT' : jStar ≤ T := hjj.trans hjT
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hqv := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmv
  have hqppd : qp.PosDef := Recurrence.posDef_of_isRoundedGrid hqp
  have hqvpd : qv.PosDef := Recurrence.posDef_of_isRoundedGrid hqv
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ :=
    Transport.maximal_filling hqvpd hqppd U j (0 : Vec d)
  let theta : ℤ → ℝ := fun a => ∑ w ∈ Z a,
    (volume (adaptedCellAt qp a w)).toReal /
      (volume (adaptedCellTranslate qv j 0)).toReal
  let F : ℤ → FullBlockMat d := fun a =>
    toFullBlockMat (adaptedMean P qp a)
  have hzero : adaptedCellTranslate qv j 0 = adaptedCell qv j := by
    simp [adaptedCellTranslate]
  have hselected : ∀ a : ℤ, ∀ w ∈ Z a,
      adaptedCellAt qp a w ⊆ centeredCube d M := by
    intro a w hw'
    have hw'' : w ∈ Transport.fillingIndex qp U
        (adaptedCellTranslate qv j 0) a := by
      rw [← hZ a]
      exact Finset.mem_coe.mpr hw'
    exact (Transport.adaptedCellAt_subset_of_mem_fillingIndex hw'').trans <| by
      rw [hzero]
      exact hcont qv (Or.inr rfl) j hjj hjT
  have hZat : ∀ a, ↑(Z a) = Transport.fillingIndex qp U
      (adaptedCellAt qv j 0) a := by
    intro a
    simpa only [PortableHistory.adaptedCellAt_zero, hzero] using hZ a
  have hraw := Transport.adaptedMean_le_filling_rows (P := P) (g := g) (E := E)
    (Ψ := Ψ) (K := K) (Cd := Cd) (Y := Y)
    (Khop := gridRatio qp qv) (n := U) (j := j) (z := 0)
    (Z := Z) (by omega : 1 ≤ d) (le_trans zero_le_one hCd) hg1 hE hEpd
    hstat hY hmp hmv hqp hqv le_rfl hjl hjj hZat
    (fun a w hw' => hselected a w hw') (by
      rw [PortableHistory.adaptedCellAt_zero]
      exact hcont qv (Or.inr rfl) j hjj hjT)
  have hraw' : toFullBlockMat (adaptedMean P qv j) ≤
      (∑ a ∈ Finset.Icc jStar U, theta a • F a) +
        (6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv *
          boundaryConst Cd g mp * zetaG g * (3 : ℝ) ^ (jStar - j) *
            ∫ a, Y a ∂P) • toFullBlockMat E := by
    simpa only [qp, qv, U, theta, F, PortableHistory.adaptedCellAt_zero, hzero] using hraw
  have htheta0 : ∀ a ∈ Finset.Icc jStar U, 0 ≤ theta a := by
    intro a _
    exact Finset.sum_nonneg fun w _ =>
      div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hmass : ∑ a ∈ Finset.Icc jStar U, theta a ≤ 1 := by
    dsimp only [theta]
    exact Transport.sum_relative_volume_le_one hqvpd hqppd hZ
  have hrow : ∀ a ∈ Finset.Icc jStar (U - 1),
      theta a ≤ 6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv *
        (3 : ℝ) ^ (a - j) := by
    intro a ha
    dsimp only [theta]
    exact Transport.sum_relative_volume_row_le_hop (by omega : 1 ≤ d) hqvpd hqppd
      (by have := (Finset.mem_Icc.mp ha).2; omega) (hZ a) le_rfl
  have hendpoint : theta U • F U ≤ F U := by
    have hUmem : U ∈ Finset.Icc jStar U :=
      Finset.mem_Icc.mpr ⟨by simpa only [U] using hjl, le_rfl⟩
    have hthetaU : theta U ≤ 1 :=
      (Finset.single_le_sum (f := theta) htheta0 hUmem).trans hmass
    have hFps : (F U).PosSemidef := by
      dsimp only [F]
      exact (Recurrence.posDef_toFullBlockMat_adaptedMean hqp U
        (Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hmp hqp
          (by simpa only [U] using hjl)
          (hcont qp (Or.inl rfl) U (by simpa only [U] using hjl)
            (by dsimp only [U]; omega)))).posSemidef
    refine Matrix.le_iff.mpr ?_
    simpa only [sub_smul, one_smul] using hFps.smul (sub_nonneg.mpr hthetaU)
  have hearly : ∑ a ∈ Finset.Icc jStar (U - 1), theta a • F a ≤
      ∑ a ∈ Finset.Icc jStar (U - 1),
        (6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv *
          (3 : ℝ) ^ (a - j)) • F a := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hFa : (F a).PosSemidef := by
      dsimp only [F]
      have haj := (Finset.mem_Icc.mp ha).1
      exact (Recurrence.posDef_toFullBlockMat_adaptedMean hqp a
        (Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hmp hqp haj
          (hcont qp (Or.inl rfl) a haj (by
            have := (Finset.mem_Icc.mp ha).2
            dsimp only [U] at this
            omega)))).posSemidef
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hFa.smul (sub_nonneg.mpr (hrow a ha))
  have hsplit : ∑ a ∈ Finset.Icc jStar U, theta a • F a =
      (∑ a ∈ Finset.Icc jStar (U - 1), theta a • F a) +
        theta U • F U := by
    have hnot : U ∉ Finset.Icc jStar (U - 1) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      omega
    rw [← Finset.insert_Icc_sub_one_right_eq_Icc
      (by simpa only [U] using hjl), Finset.sum_insert hnot]
    abel
  have hselectedRows : ∑ a ∈ Finset.Icc jStar U, theta a • F a ≤
      F U + ∑ a ∈ Finset.Icc jStar (U - 1),
        (6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv *
          (3 : ℝ) ^ (a - j)) • F a := by
    rw [hsplit]
    simpa only [add_comm] using add_le_add hearly hendpoint
  have hsource := below_start_mean_le_terminal hCd hg0 hg1 hE hEpd hQ hw hY
    (mp := mp) (mv := mv) (mr := mp) hmp hqp (j := j) (t := T) hjj hjT'
    (hcont qp (Or.inl rfl) T hjT' le_rfl)
  have hstep := hraw'.trans (add_le_add hselectedRows hsource)
  dsimp only [theta, F] at hstep
  simpa only [qp, qv, U, add_assoc] using hstep

end

end Bridge
end HighContrast
end Homogenization
