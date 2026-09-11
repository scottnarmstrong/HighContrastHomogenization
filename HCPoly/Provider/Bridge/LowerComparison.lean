/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.LowerComparisonRaw
import HCPoly.Provider.Bridge.DecaySums
import HCPoly.Provider.Bridge.GuardedDivision
import HCPoly.Provider.Bridge.LinearDrift
import HCPoly.Provider.Bridge.SourceCoefficients
import HCPoly.Provider.ShortHop.SourceCoefficient

/-!
# Lower two-grid comparison

The packed row has mass at most one, so the raw hybrid estimate can be solved
monotonically and absorbed into the printed guarded lower error.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd Q C : ℝ} {jStar M : ℤ}
  {Y : CoeffSpace d → ℝ}

/-- The reverse hybrid filling gives the printed lower comparison once the
geometric and continued source rows are absorbed by the common constant. -/
theorem lower_comparison [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hC0 : 0 ≤ C)
    (hCrow : (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
      (3 * (2 * (d : ℝ) * Real.sqrt d +
          (2 * (d : ℝ) * Real.sqrt d) *
            (2 * (d : ℝ) * Real.sqrt d) * 2 *
              (1 + 6 * Real.sqrt d) ^ (d - 1)) +
        2 * (d : ℝ) * Real.sqrt d) ≤ C)
    (hCsrc : 18 * (d : ℝ) * Real.sqrt d *
      (2 * (d : ℝ) * Real.sqrt d +
        (2 * (d : ℝ) * Real.sqrt d) *
          (2 * (d : ℝ) * Real.sqrt d) * 2 *
            (1 + 6 * Real.sqrt d) ^ (d - 1)) ≤ C)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hrhog : rho ≤ 1 - g)
    {n l : ℤ} (hl : 0 ≤ l) (hjn : jStar ≤ n)
    (hsmall : C * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
      (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ j : ℤ, jStar ≤ j → j ≤ n + l →
        adaptedCell r j ⊆ centeredCube d M) :
    BlockMatLoewnerLE
      (blockScale
        (-bridgeErrLower C Cd g rho
          (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
          P E jStar mp mv n l)
        (adaptedMean P (roundedGrid jStar mp) (n + l)))
      (blockSub (adaptedMean P (roundedGrid jStar mv) n)
        (adaptedMean P (roundedGrid jStar mp) (n + l))) := by
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let Kpv : ℝ := gridRatio qp qv
  let T : ℤ := n + l
  let N : ℝ := (T : ℝ) - (jStar : ℝ)
  let Dp : ℝ := linearDrift P rho qp jStar T
  let fast : ℝ := (3 : ℝ) ^ (-(1 - g) * N)
  let slow : ℝ := (1 + N) * (3 : ℝ) ^ (-rho * N)
  let row : ℝ := (3 : ℝ) ^ (-(l : ℝ)) +
    (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) * Dp
  let Cg : ℝ := 2 * (d : ℝ) * Real.sqrt d +
    (2 * (d : ℝ) * Real.sqrt d) *
      (2 * (d : ℝ) * Real.sqrt d) * 2 *
        (1 + 6 * Real.sqrt d) ^ (d - 1)
  let D0 : ℝ := 2 * (d : ℝ) * Real.sqrt d
  let D : ℝ := 3 * Cg + D0
  have hjT : jStar ≤ T := by dsimp only [T]; omega
  have hN0 : 0 ≤ N := by
    have hjTR : (jStar : ℝ) ≤ (T : ℝ) := by exact_mod_cast hjT
    dsimp only [N]
    linarith only [hjTR]
  have hK0 : 0 ≤ Kpv := by
    exact le_trans zero_le_one (Transport.one_le_gridRatio qp qv)
  have hCK0 : 0 ≤ C * Kpv := mul_nonneg hC0 hK0
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hqv := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmv
  have hdef := Transport.definedness_of_isWindowMultiplier hd hstat hE hQ hw hY
    hmp hmv (b := T) (by simpa only [T] using hcont)
  have hfinp : HasFiniteAdaptedMean P qp T :=
    (hdef.1 qp (Or.inl rfl) T hjT le_rfl).1
  have hfinv : HasFiniteAdaptedMean P qv n :=
    (hdef.1 qv (Or.inr rfl) n hjn (by dsimp only [T]; omega)).1
  have hmeanp : (toFullBlockMat (adaptedMean P qp T)).PosSemidef :=
    (Recurrence.posDef_toFullBlockMat_adaptedMean hqp T hfinp).posSemidef
  have hmeanv : (toFullBlockMat (adaptedMean P qv n)).PosSemidef :=
    (Recurrence.posDef_toFullBlockMat_adaptedMean hqv n hfinv).posSemidef
  have hD0' : 0 ≤ Dp := by
    dsimp only [Dp]
    exact linearDrift_nonneg hstat hqp le_rfl hjT
      (fun j hj hjT' => (hdef.1 qp (Or.inl rfl) j hj hjT').1) rho
  have hrow0 : 0 ≤ row := by
    dsimp only [row]
    positivity
  have hsrc0 : 0 ≤ bridgeSrcCoeff Cd g E jStar mv mp :=
    le_trans zero_le_one
      (ShortHop.one_le_bridgeSrcCoeff (le_trans zero_le_one hCd) hg1 E jStar mv mp)
  have hcont0 : 0 ≤ bridgeContCoeff Cd g E jStar mp mv mp :=
    ShortHop.zero_le_bridgeContCoeff (le_trans zero_le_one hCd) hg1 E jStar mp mv mp
  have hearly0 : 0 ≤ bridgeEarlyCoeff Cd g E mv mp :=
    ShortHop.zero_le_bridgeEarlyCoeff (le_trans zero_le_one hCd) hg1 E mv mp
  have hcontSrc : bridgeContCoeff Cd g E jStar mp mv mp ≤
      bridgeSrcCoeff Cd g E jStar mv mp :=
    (le_add_of_nonneg_right hearly0).trans
      (ordered_coefficients_le_bridgeSrcCoeff Cd g E jStar mv mp).2.2.2
  have hfast : fast ≤ slow := by
    dsimp only [fast, slow]
    exact fast_decay_le_linear_slow_decay hN0 hrhog
  have hfast0 : 0 ≤ fast := by dsimp only [fast]; positivity
  have hslow0 : 0 ≤ slow := by
    dsimp only [slow]
    exact mul_nonneg (by linarith only [hN0]) (Real.rpow_nonneg (by norm_num) _)
  have hden : 0 < 1 - C * Kpv * (3 : ℝ) ^ (-(l : ℝ)) := by
    exact one_sub_pos_of_le_half (by simpa only [Kpv, qp, qv] using hsmall)
  have hratio0 : 0 ≤ C * Kpv * (3 : ℝ) ^ (-(l : ℝ)) := by
    positivity
  have hCKdiv : C * Kpv ≤
      C * Kpv / (1 - C * Kpv * (3 : ℝ) ^ (-(l : ℝ))) := by
    rw [le_div_iff₀ hden]
    calc
      C * Kpv * (1 - C * Kpv * (3 : ℝ) ^ (-(l : ℝ))) ≤
          C * Kpv * 1 :=
        mul_le_mul_of_nonneg_left (sub_le_self 1 hratio0) hCK0
      _ = C * Kpv := by ring
  have hmain :
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * Kpv * row ≤
        C * Kpv / (1 - C * Kpv * (3 : ℝ) ^ (-(l : ℝ))) * row := by
    have hfirst : (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * Kpv ≤
        C * Kpv := by
      exact mul_le_mul_of_nonneg_right (by simpa only [D, Cg, D0] using hCrow) hK0
    exact mul_le_mul_of_nonneg_right (hfirst.trans hCKdiv) hrow0
  have hsource :
      18 * (d : ℝ) * Real.sqrt d * Cg *
          bridgeContCoeff Cd g E jStar mp mv mp * fast ≤
        C * bridgeSrcCoeff Cd g E jStar mv mp * slow := by
    have hcoef : 18 * (d : ℝ) * Real.sqrt d * Cg *
        bridgeContCoeff Cd g E jStar mp mv mp ≤
          C * bridgeSrcCoeff Cd g E jStar mv mp :=
      mul_le_mul (by simpa only [Cg] using hCsrc) hcontSrc hcont0 hC0
    exact mul_le_mul hcoef hfast hfast0 (mul_nonneg hC0 hsrc0)
  have hcoef :
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * Kpv * row +
          18 * (d : ℝ) * Real.sqrt d * Cg *
            bridgeContCoeff Cd g E jStar mp mv mp * fast ≤
        bridgeErrLower C Cd g rho Kpv P E jStar mp mv n l := by
    have h := add_le_add hmain hsource
    simpa only [bridgeErrLower, bridgeCmpRemainder, qp, qv, Kpv, T, N, Dp,
      fast, slow, row, mul_assoc] using h
  obtain ⟨alpha, -, halpha, hraw⟩ := lower_comparison_raw hd hCd hg0 hg1 hE
    hEpd hstat hQ hw hY hmp hmv hrho0 hrho1 (Cg := Cg) (D0 := D0)
      (D := D) rfl rfl rfl hl hjn hcont
  have halphaMean : alpha • toFullBlockMat (adaptedMean P qv n) ≤
      toFullBlockMat (adaptedMean P qv n) := by
    have h : alpha • toFullBlockMat (adaptedMean P qv n) ≤
        (1 : ℝ) • toFullBlockMat (adaptedMean P qv n) := by
      refine Matrix.le_iff.mpr ?_
      rw [← sub_smul]
      exact hmeanv.smul (sub_nonneg.mpr halpha)
    simpa only [one_smul] using h
  have hscaled :
      ((1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * Kpv * row +
          18 * (d : ℝ) * Real.sqrt d * Cg *
            bridgeContCoeff Cd g E jStar mp mv mp * fast) •
          toFullBlockMat (adaptedMean P qp T) ≤
        bridgeErrLower C Cd g rho Kpv P E jStar mp mv n l •
          toFullBlockMat (adaptedMean P qp T) := by
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hmeanp.smul (sub_nonneg.mpr hcoef)
  have hstep := hraw.trans (add_le_add halphaMean hscaled)
  apply blockMatLoewnerLE_of_le
  rw [toFullBlockMat_blockScale, Recurrence.toFullBlockMat_blockSub,
    le_sub_iff_add_le]
  have hrearranged :
      toFullBlockMat (adaptedMean P qp T) -
          bridgeErrLower C Cd g rho Kpv P E jStar mp mv n l •
            toFullBlockMat (adaptedMean P qp T) ≤
        toFullBlockMat (adaptedMean P qv n) := by
    rw [sub_le_iff_le_add]
    simpa only [add_comm] using hstep
  simpa only [neg_smul, add_comm, qp, qv, Kpv, T] using hrearranged

end

end Bridge
end HighContrast
end Homogenization
