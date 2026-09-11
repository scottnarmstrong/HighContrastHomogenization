/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.UpperComparisonRaw
import HCPoly.Provider.Bridge.DecaySums
import HCPoly.Provider.Bridge.LinearDrift
import HCPoly.Provider.Bridge.SourceCoefficients
import HCPoly.Provider.ShortHop.SourceCoefficient

/-!
# Upper two-grid comparison

The raw maximal-filling row is absorbed into the printed upper comparison
error once the common bridge constant dominates its geometric coefficients.
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

/-- The maximal old-grid filling gives the printed upper comparison after its
dimensional row and continued source coefficients are absorbed. -/
theorem upper_comparison [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hC0 : 0 ≤ C)
    (hCrow : (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
      (6 * (d : ℝ) * Real.sqrt d) ≤ C)
    (hCsrc : 18 * (d : ℝ) * Real.sqrt d ≤ C)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hrhog : rho ≤ 1 - g)
    {n l : ℤ} (hl : 0 ≤ l) (hjn : jStar ≤ n - l)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ j : ℤ, jStar ≤ j → j ≤ n + l →
        adaptedCell r j ⊆ centeredCube d M) :
    BlockMatLoewnerLE
      (blockSub (adaptedMean P (roundedGrid jStar mv) n)
        (adaptedMean P (roundedGrid jStar mp) (n - l)))
      (blockScale
        (bridgeErrUpper C Cd g rho
          (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
          P E jStar mp mv n l)
        (adaptedMean P (roundedGrid jStar mp) n)) := by
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let Kpv : ℝ := gridRatio qp qv
  let N : ℝ := (n : ℝ) - (jStar : ℝ)
  let Dp : ℝ := linearDrift P rho qp jStar n
  let fast : ℝ := (3 : ℝ) ^ (-(1 - g) * N)
  let slow : ℝ := (1 + N) * (3 : ℝ) ^ (-rho * N)
  let row : ℝ := (3 : ℝ) ^ (-(l : ℝ)) +
    (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) * Dp
  have hjn0 : jStar ≤ n := by omega
  have hN0 : 0 ≤ N := by
    have hjnR : (jStar : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn0
    dsimp only [N]
    linarith only [hjnR]
  have hK0 : 0 ≤ Kpv := by
    exact le_trans zero_le_one (Transport.one_le_gridRatio qp qv)
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hdef := Transport.definedness_of_isWindowMultiplier hd hstat hE hQ hw hY
    hmp hmv (b := n + l) hcont
  have hfin : HasFiniteAdaptedMean P qp n :=
    (hdef.1 qp (Or.inl rfl) n hjn0 (by omega)).1
  have hmean : (toFullBlockMat (adaptedMean P qp n)).PosSemidef :=
    (Recurrence.posDef_toFullBlockMat_adaptedMean hqp n hfin).posSemidef
  have hD0 : 0 ≤ Dp := by
    dsimp only [Dp]
    exact linearDrift_nonneg hstat hqp le_rfl hjn0
      (fun j hj hnj => (hdef.1 qp (Or.inl rfl) j hj (hnj.trans (by omega))).1) rho
  have hrow0 : 0 ≤ row := by
    dsimp only [row]
    positivity
  have hsrc0 : 0 ≤ bridgeSrcCoeff Cd g E jStar mp mv :=
    le_trans zero_le_one
      (ShortHop.one_le_bridgeSrcCoeff (le_trans zero_le_one hCd) hg1 E jStar mp mv)
  have hcont0 : 0 ≤ bridgeContCoeff Cd g E jStar mp mv mp :=
    ShortHop.zero_le_bridgeContCoeff (le_trans zero_le_one hCd) hg1 E jStar mp mv mp
  have hearly0 : 0 ≤ bridgeEarlyCoeff Cd g E mv mp :=
    ShortHop.zero_le_bridgeEarlyCoeff (le_trans zero_le_one hCd) hg1 E mv mp
  have hcontSrc : bridgeContCoeff Cd g E jStar mp mv mp ≤
      bridgeSrcCoeff Cd g E jStar mp mv :=
    (le_add_of_nonneg_right hearly0).trans
      (ordered_coefficients_le_bridgeSrcCoeff Cd g E jStar mp mv).1
  have hfast : fast ≤ slow := by
    dsimp only [fast, slow]
    exact fast_decay_le_linear_slow_decay hN0 hrhog
  have hfast0 : 0 ≤ fast := by dsimp only [fast]; positivity
  have hslow0 : 0 ≤ slow := by
    dsimp only [slow]
    exact mul_nonneg (by linarith only [hN0]) (Real.rpow_nonneg (by norm_num) _)
  have hmain :
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
          (6 * (d : ℝ) * Real.sqrt d) * Kpv * row ≤
        C * Kpv * row := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCrow hK0) hrow0
  have hsource :
      18 * (d : ℝ) * Real.sqrt d *
          bridgeContCoeff Cd g E jStar mp mv mp * fast ≤
        C * bridgeSrcCoeff Cd g E jStar mp mv * slow := by
    have hcoef : 18 * (d : ℝ) * Real.sqrt d *
        bridgeContCoeff Cd g E jStar mp mv mp ≤
          C * bridgeSrcCoeff Cd g E jStar mp mv :=
      mul_le_mul hCsrc hcontSrc hcont0 hC0
    exact mul_le_mul hcoef hfast hfast0 (mul_nonneg hC0 hsrc0)
  have hcoef :
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
            (6 * (d : ℝ) * Real.sqrt d) * Kpv * row +
          18 * (d : ℝ) * Real.sqrt d *
            bridgeContCoeff Cd g E jStar mp mv mp * fast ≤
        bridgeErrUpper C Cd g rho Kpv P E jStar mp mv n l := by
    have h := add_le_add hmain hsource
    simpa only [bridgeErrUpper, bridgeCmpRemainder, qp, Kpv, N, Dp, fast,
      slow, row, mul_assoc] using h
  have hraw := upper_comparison_raw hd hCd hg0 hg1 hE hEpd hstat hQ hw hY
    hmp hmv hrho0 hrho1 hl hjn hcont
  have hscaled :
      ((1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
            (6 * (d : ℝ) * Real.sqrt d) * Kpv * row +
          18 * (d : ℝ) * Real.sqrt d *
            bridgeContCoeff Cd g E jStar mp mv mp * fast) •
          toFullBlockMat (adaptedMean P qp n) ≤
        bridgeErrUpper C Cd g rho Kpv P E jStar mp mv n l •
          toFullBlockMat (adaptedMean P qp n) := by
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hmean.smul (sub_nonneg.mpr hcoef)
  have hstep := hraw.trans (add_le_add le_rfl hscaled)
  apply blockMatLoewnerLE_of_le
  rw [Recurrence.toFullBlockMat_blockSub, toFullBlockMat_blockScale,
    sub_le_iff_le_add']
  simpa only [qp, qv, Kpv, N, Dp, fast, row, add_comm] using hstep

end

end Bridge
end HighContrast
end Homogenization
