/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ShiftedDriftRaw

/-!
# Shifted determinant drift

One structural constant absorbs the normalization slack, boundary mass, shifted
old-drift convolution, and source coefficient in the printed remainder.
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

/-- The shifted new-grid drift is controlled by the printed separation, old
drift, and source rows once the common constant dominates four structural
coefficients. -/
theorem shifted_drift [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hC1 : 1 ≤ C)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) (hrhog : rho ≤ 1 - g)
    (hCeta : 4 * (d : ℝ) * (1 / (1 - (3 : ℝ) ^ (-rho))) ≤ C)
    (hCmass : 2 * ((6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
      (1 / (1 - (3 : ℝ) ^ (-rho))) *
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))) ≤ C)
    (hCdrift : 2 * ((1 / (1 - (3 : ℝ) ^ (-rho))) +
      (6 * (d : ℝ) * Real.sqrt d) *
        (1 / (1 - (3 : ℝ) ^ (-rho))) *
        (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) ≤ C)
    (hCsrc : 2 * (2 * (d : ℝ) +
      (18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ))) ≤ C)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
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
      C *
        (eta +
          gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
            (3 : ℝ) ^ (-(l : ℝ)) +
          (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
            (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
              linearDrift P rho (roundedGrid jStar mp) jStar (n + l) +
          bridgeShiftedRemainder C Cd g rho E jStar mp mv n l) := by
  let Kpv : ℝ := gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)
  let massBase : ℝ := Kpv * (3 : ℝ) ^ (-(l : ℝ))
  let driftBase : ℝ := (1 + Kpv) * (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
    linearDrift P rho (roundedGrid jStar mp) jStar (n + l)
  let sourceBase : ℝ := bridgeSrcCoeff Cd g E jStar mp mv *
    (3 : ℝ) ^ (rho * (l : ℝ)) *
      (1 + ((n : ℝ) - (jStar : ℝ))) *
        (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ)))
  let Amass : ℝ := (6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
    (1 / (1 - (3 : ℝ) ^ (-rho))) *
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))
  let Adrift : ℝ := (1 / (1 - (3 : ℝ) ^ (-rho))) +
    (6 * (d : ℝ) * Real.sqrt d) *
      (1 / (1 - (3 : ℝ) ^ (-rho))) *
      (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))
  let Asource : ℝ := 2 * (d : ℝ) +
    (18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ))
  have hjn0 : jStar ≤ n := by omega
  have hK0 : 0 ≤ Kpv := by
    dsimp only [Kpv]
    exact le_trans zero_le_one (Transport.one_le_gridRatio _ _)
  have hD0 : 0 ≤ linearDrift P rho (roundedGrid jStar mp) jStar (n + l) := by
    have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
    have hdef := Transport.definedness_of_isWindowMultiplier hd hstat hE hQ hw hY
      hmp hmv (b := n + l) hcont
    exact linearDrift_nonneg hstat hqp le_rfl (by omega)
      (fun j hj hjT => (hdef.1 _ (Or.inl rfl) j hj hjT).1) rho
  have hsrc0 : 0 ≤ bridgeSrcCoeff Cd g E jStar mp mv :=
    le_trans zero_le_one
      (ShortHop.one_le_bridgeSrcCoeff (le_trans zero_le_one hCd) hg1 E jStar mp mv)
  have hnjR : (jStar : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn0
  have hmass0 : 0 ≤ massBase := by dsimp only [massBase]; positivity
  have hdrift0 : 0 ≤ driftBase := by dsimp only [driftBase]; positivity
  have hsource0 : 0 ≤ sourceBase := by
    dsimp only [sourceBase]
    have hfront : 0 ≤ 1 + ((n : ℝ) - (jStar : ℝ)) := by
      linarith only [hnjR]
    positivity
  have hraw := shifted_drift_raw hd hCd hg0 hg1 hE hEpd hstat hQ hw hY
    hmp hmv hrho hrho1 hrhog hl hjn heta0 heta4 hBA hcont
  have hraw' :
      linearDrift P rho (roundedGrid jStar mv) jStar n ≤
        2 * (Amass * massBase + Adrift * driftBase + Asource * sourceBase) +
          (4 * (d : ℝ) * (1 / (1 - (3 : ℝ) ^ (-rho)))) * eta := by
    simpa only [Kpv, massBase, driftBase, sourceBase, Amass, Adrift, Asource,
      mul_assoc, mul_comm, mul_left_comm] using hraw
  have heta := mul_le_mul_of_nonneg_right hCeta heta0
  have hmass := mul_le_mul_of_nonneg_right hCmass hmass0
  have hdrift := mul_le_mul_of_nonneg_right hCdrift hdrift0
  have hsrcC : 2 * Asource ≤ C := by simpa only [Asource] using hCsrc
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hCC : C ≤ C * C := by
    nth_rewrite 1 [← mul_one C]
    exact mul_le_mul_of_nonneg_left hC1 hC0
  have hsource := mul_le_mul_of_nonneg_right (hsrcC.trans hCC) hsource0
  have habsorb :
      2 * (Amass * massBase + Adrift * driftBase + Asource * sourceBase) +
          (4 * (d : ℝ) * (1 / (1 - (3 : ℝ) ^ (-rho)))) * eta ≤
        C * (eta + massBase + driftBase + C * sourceBase) := by
    have hmass' : (2 * Amass) * massBase ≤ C * massBase := by
      simpa only [Amass] using hmass
    have hdrift' : (2 * Adrift) * driftBase ≤ C * driftBase := by
      simpa only [Adrift] using hdrift
    linarith only [heta, hmass', hdrift', hsource]
  have h := hraw'.trans habsorb
  simpa only [Kpv, massBase, driftBase, sourceBase, Amass, Adrift, Asource,
    bridgeShiftedRemainder, mul_assoc] using h

end

end Bridge
end HighContrast
end Homogenization
