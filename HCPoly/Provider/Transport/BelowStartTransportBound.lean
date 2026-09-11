/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.GridTransportCenteredConstants
import HCPoly.Provider.Transport.WindowTerminalNormalization

/-!
# The concrete below-start maximum of grid transport

This packages the terminal normalization and source-coefficient comparison for
the exact below-start scalar appearing in every cell majorant.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The exact shared below-start maximum of the target family is charged to one
transported source remainder. -/
theorem below_start_target_max_le_transport [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hd : 1 ≤ d) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1)
    {Q : ℕ} (hQ : 2 ≤ Q) {rhoMax a Khop : ℝ} (hrho : rhoMax < 1)
    (hKhop : 1 ≤ Khop) (haQrho : a ≤ (Q : ℝ) * rhoMax)
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} (hCd : 1 ≤ Cd)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    {jStar M : ℤ} (hw : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu mu' : Mat d} (hmu' : mu'.PosDef)
    (hKgrid : gridRatio (roundedGrid jStar mu)
      (roundedGrid jStar mu') ≤ Khop)
    {n : ℤ} (hjn : jStar ≤ n)
    (hcontn : adaptedCell (roundedGrid jStar mu') n ⊆ centeredCube d M)
    (hFpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar mu') n))
    {iota : Type*} [DecidableEq iota] (s : Finset iota) (hs : s.Nonempty)
    (lev : iota → ℤ) (hlev : ∀ i ∈ s, jStar ≤ lev i) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
        (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
          schattenSize (Q : ℝ)
            (blockScale
              (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu *
                zetaG g * (3 : ℝ) ^ (jStar - lev i) *
                (Y x - ∫ y, Y y ∂P)) E)
            (adaptedMean P (roundedGrid jStar mu') n)) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal
        (centeredBelowStartConst d Q Khop *
          transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu' n) := by
  have hCd0 : 0 ≤ Cd := le_trans zero_le_one hCd
  have hCdpos : 0 < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hKhop0 : 0 ≤ Khop := le_trans zero_le_one hKhop
  have hq' := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu'
  set U : ℝ := ∫ x, Y x ∂P with hU
  have hU0 : 0 ≤ U := by
    rw [hU]
    exact le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  have hU1 : 1 ≤ U := by
    rw [hU]
    exact one_le_integral_of_isWindowMultiplier hY
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hU2 : U ≤ 2 := by
    have hnorm := le_trans (ofReal_integral_le_lqNorm hY hQ1)
      (lqNorm_le_two hQ1 hw hY)
    have hof : ENNReal.ofReal U ≤ ENNReal.ofReal 2 := by
      simpa only [hU, show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by norm_num] using hnorm
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hof
  let A : ℝ := 6 * (d : ℝ) * Real.sqrt d * Khop *
    boundaryConst Cd g mu * zetaG g
  let D : ℝ := A * U *
    (kappaRef E * (boundaryConst Cd g mu' * U))
  let Lam : ℝ := 18 * (d : ℝ) * Real.sqrt d * Khop
  have hB0 : 0 ≤ boundaryConst Cd g mu := zero_le_boundaryConst hCd0 hg1 mu
  have hB0' : 0 ≤ boundaryConst Cd g mu' := zero_le_boundaryConst hCd0 hg1 mu'
  have hzeta0 : 0 ≤ zetaG g := (zero_lt_zetaG hg1).le
  have hkappa0 : 0 ≤ kappaRef E := by
    rw [kappaRef, blockSize]
    exact Real.sInf_nonneg fun _ hx => hx.1
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  have hD0 : 0 ≤ D := by simp only [D]; positivity
  have hLam1 : 1 ≤ Lam := by
    have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR1
    simp only [Lam]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hdR1) hsqrt1) hKhop
  have hblock := blockSize_adaptedMean_le hCdpos hg1 hE hEpd hY hmu' hq'
    hjn hcontn
  have hAD : A * blockSize E
        (adaptedMean P (roundedGrid jStar mu') n) ≤ D := by
    calc
      A * blockSize E (adaptedMean P (roundedGrid jStar mu') n) ≤
          A * (kappaRef E * (boundaryConst Cd g mu' * U)) :=
        mul_le_mul_of_nonneg_left (by simpa only [hU] using hblock) hA0
      _ ≤ A * U * (kappaRef E * (boundaryConst Cd g mu' * U)) := by
        have hfac : A ≤ A * U := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hU1 hA0
        exact mul_le_mul_of_nonneg_right hfac
          (mul_nonneg hkappa0 (mul_nonneg hB0' hU0))
      _ = D := rfl
  have hDcont : D ≤ Lam * transportContCoeff Cd g E jStar mu mu' := by
    simpa only [D, A, Lam, hU] using
      srcRow_coefficient_absorbed hd hg0 hg1 hCd E mu mu' hKgrid hU0 hU2
  have hDsrc : D ≤ Lam * transportSrcCoeff Cd g E jStar mu mu' :=
    hDcont.trans (mul_le_mul_of_nonneg_left
      (transportContCoeff_le_transportSrcCoeff hCd0 hg1 E jStar mu mu')
      (le_trans zero_le_one hLam1))
  have hraw := below_start_majorant_max_le_source_remainder hQ hw hY hE
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu') n) hFpd
    hrho hA0 hD0 hAD s hs lev hlev hLam1 mu mu' hCd0 hg1 hDsrc hjn haQrho
  simpa only [A, Lam, centeredBelowStartConst, mul_assoc] using hraw

end

end Transport
end HighContrast
end Homogenization
