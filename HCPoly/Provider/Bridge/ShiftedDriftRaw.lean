/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ShiftedGapSum
import HCPoly.Provider.Bridge.ShiftedSumComparison
import HCPoly.Provider.Bridge.LinearDrift

/-!
# Raw shifted-drift estimate

The new-grid determinant increments are first enlarged to terminal gaps, then
normalized by the old-grid terminal block.  The complete old-terminal gap sum
supplies the separation, shifted old-drift, and source rows.
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

/-- Before structural constants are absorbed, the shifted drift has the three
explicit old-terminal rows and the normalization-change slack. -/
theorem shifted_drift_raw [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) (hrhog : rho ≤ 1 - g)
    {n l : ℤ} (hl : 1 ≤ l) (hjn : jStar ≤ n - l)
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta4 : eta ≤ 1 / 4)
    (hBA : BlockMatLoewnerLE
      (blockScale (1 - eta)
        (adaptedMean P (roundedGrid jStar mp) (n + l)))
      (adaptedMean P (roundedGrid jStar mv) n))
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ a : ℤ, jStar ≤ a → a ≤ n + l →
        adaptedCell r a ⊆ centeredCube d M) :
    linearDrift P rho (roundedGrid jStar mv) jStar n ≤
      2 *
        (((6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
              (1 / (1 - (3 : ℝ) ^ (-rho))) *
              (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))) *
            gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
              (3 : ℝ) ^ (-(l : ℝ)) +
          ((1 / (1 - (3 : ℝ) ^ (-rho))) +
              (6 * (d : ℝ) * Real.sqrt d) *
                (1 / (1 - (3 : ℝ) ^ (-rho))) *
                (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
            (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
              (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
                linearDrift P rho (roundedGrid jStar mp) jStar (n + l) +
          (2 * (d : ℝ) +
              (18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ))) *
            bridgeSrcCoeff Cd g E jStar mp mv *
              (3 : ℝ) ^ (rho * (l : ℝ)) *
              (1 + ((n : ℝ) - (jStar : ℝ))) *
                (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ)))) +
        4 * (d : ℝ) * eta * (1 / (1 - (3 : ℝ) ^ (-rho))) := by
  classical
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let T : ℤ := n + l
  let A : FullBlockMat d := toFullBlockMat (adaptedMean P qv n)
  let B : FullBlockMat d := toFullBlockMat (adaptedMean P qp T)
  let F : ℤ → FullBlockMat d := fun j => toFullBlockMat (adaptedMean P qv j)
  let R : ℝ :=
    ((6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
          (1 / (1 - (3 : ℝ) ^ (-rho))) *
          (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))) * gridRatio qp qv *
        (3 : ℝ) ^ (-(l : ℝ)) +
    ((1 / (1 - (3 : ℝ) ^ (-rho))) +
        (6 * (d : ℝ) * Real.sqrt d) *
          (1 / (1 - (3 : ℝ) ^ (-rho))) *
          (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
      (1 + gridRatio qp qv) * (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
        linearDrift P rho qp jStar T +
    (2 * (d : ℝ) + (18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ))) *
      bridgeSrcCoeff Cd g E jStar mp mv * (3 : ℝ) ^ (rho * (l : ℝ)) *
        (1 + ((n : ℝ) - (jStar : ℝ))) *
          (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ)))
  have hjn0 : jStar ≤ n := by omega
  have hjT : n ≤ T := by dsimp only [T]; omega
  have hjStarT : jStar ≤ T := hjn0.trans hjT
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hqv := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmv
  have hdef := Transport.definedness_of_isWindowMultiplier hd hstat hE hQ hw hY
    hmp hmv (b := T) (by simpa only [T] using hcont)
  have hApos : A.PosDef := by
    dsimp only [A]
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hqv n
      ((hdef.1 qv (Or.inr rfl) n hjn0 (by dsimp only [T]; omega)).1)
  have hBpos : B.PosDef := by
    dsimp only [B]
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hqp T
      ((hdef.1 qp (Or.inl rfl) T hjStarT le_rfl).1)
  have hFpsd : ∀ j ∈ Finset.Ico jStar n, (F j).PosSemidef := by
    intro j hj
    dsimp only [F]
    exact (Recurrence.posDef_toFullBlockMat_adaptedMean hqv j
      ((hdef.1 qv (Or.inr rfl) j (Finset.mem_Ico.mp hj).1 (by
        have := (Finset.mem_Ico.mp hj).2
        dsimp only [T]
        omega)).1)).posSemidef
  have hterm : ∀ r ∈ Finset.Icc (jStar + 1) n, F n ≤ F r := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    dsimp only [F]
    exact Recurrence.toFullBlockMat_adaptedMean_le hstat hqv (by omega) hrange.2
      ((hdef.1 qv (Or.inr rfl) r (by omega) (by
        dsimp only [T]
        omega)).1)
      ((hdef.1 qv (Or.inr rfl) n hjn0 (by dsimp only [T]; omega)).1)
  have hBAfull : (1 - eta) • B ≤ A := by
    have h := (blockMatLoewnerLE_iff_le
      (isSymmetricBlockMat_blockScale (1 - eta)
        (Recurrence.isSymmetricBlockMat_adaptedMean P qp T))
      (Recurrence.isSymmetricBlockMat_adaptedMean P qv n)).mp hBA
    rw [toFullBlockMat_blockScale] at h
    simpa only [A, B, qp, qv, T] using h
  have hR := weighted_old_terminal_gaps_le hd hCd hg0 hg1 hE hEpd hstat hQ hw hY
    hmp hmv hrho hrho1 hrhog hl hjn hcont
  have hRbound : ∑ j ∈ Finset.Ico jStar n,
      (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
        Matrix.trace (B⁻¹ * (F j - B)) ≤ R := by
    simpa only [A, B, F, R, qp, qv, T] using hR
  have hK0 : 0 ≤ gridRatio qp qv :=
    le_trans zero_le_one (Transport.one_le_gridRatio qp qv)
  have hG0 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-rho)) :=
    div_nonneg zero_le_one (sub_nonneg.mpr (PortableHistory.geom_ratio_lt_one hrho).le)
  have hG10 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 - rho))) :=
    div_nonneg zero_le_one (sub_nonneg.mpr
      (PortableHistory.geom_ratio_lt_one (by linarith only [hrho1])).le)
  have hD0 : 0 ≤ linearDrift P rho qp jStar T :=
    linearDrift_nonneg hstat hqp le_rfl hjStarT
      (fun j hj hjT' => (hdef.1 qp (Or.inl rfl) j hj hjT').1) rho
  have hsrc0 : 0 ≤ bridgeSrcCoeff Cd g E jStar mp mv :=
    le_trans zero_le_one
      (ShortHop.one_le_bridgeSrcCoeff (le_trans zero_le_one hCd) hg1 E jStar mp mv)
  have hnjR : (jStar : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn0
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    have hGbase : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))) := by norm_num
    have hfront : 0 ≤ 1 + ((n : ℝ) - (jStar : ℝ)) := by
      linarith only [hnjR]
    positivity
  have hchange := weighted_terminal_gaps_le_of_sum_bound A B hApos hBpos
    heta0 heta4 hBAfull F hFpsd hR0 hRbound
  have hinc := weighted_increments_le_weighted_terminal_gaps
    (rho := rho) (b := jStar) (n := n) F hApos hterm
  have hweights := shifted_weight_sum_le hrho (b := jStar) (n := n)
  have hfinal := hinc.trans (hchange.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hweights (by positivity : 0 ≤ 4 * (d : ℝ) * eta)) _))
  have hdriftNew :
      ∑ r ∈ Finset.Icc (jStar + 1) n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - (r : ℝ))) *
          Matrix.trace ((F n)⁻¹ * (F (r - 1) - F r)) =
        linearDrift P rho qv jStar n := by
    simp only [linearDrift, F, qv, blockTrace, toFullBlockMat_ofFullBlockMat,
      Recurrence.toFullBlockMat_blockSub]
  rw [← hdriftNew]
  simpa only [F, A, B, R, qp, qv, T] using hfinal

end

end Bridge
end HighContrast
end Homogenization
