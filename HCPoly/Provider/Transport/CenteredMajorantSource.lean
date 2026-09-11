/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowCenteredSup
import HCPoly.Provider.Transport.CenteredSplit
import HCPoly.Provider.Transport.TransportConclusion

/-!
# The below-start part of a finite majorant family

The below-start fluctuation is common to all target cells, apart from its scale
coefficient.  Taking the maximum therefore costs no target multiplicity.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Scalar dilation is homogeneous for the block size. -/
theorem blockSize_blockScale_le_abs_mul {E F : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) (c : ℝ) :
    blockSize (blockScale c E) F ≤ |c| * blockSize E F := by
  rw [PortableHistory.blockSize_eq_norm (isSymmetricBlockMat_blockScale c hE) hF hFpd,
    PortableHistory.blockSize_eq_norm hE hF hFpd, Recurrence.toFullBlockMat_normalizedBlock,
    Recurrence.toFullBlockMat_normalizedBlock, toFullBlockMat_blockScale,
    Matrix.mul_smul, Matrix.smul_mul, norm_smul, Real.norm_eq_abs]

/-- The maximum of the below-start pieces over a finite target family has the
moment of the one shared centered multiplier, with no target-cardinality loss. -/
theorem finite_below_start_max_moment_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ}
    {Y : CoeffSpace d → ℝ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {F : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    {rhoMax A D : ℝ} (hrho : rhoMax < 1) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hAD : A * blockSize E F ≤ D)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (lev : ι → ℤ) {n : ℤ} (hlev : ∀ i ∈ s, jStar ≤ lev i) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
        (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
          schattenSize (Q : ℝ)
            (blockScale
              (A * (3 : ℝ) ^ (jStar - lev i) *
                (Y x - ∫ y, Y y ∂P)) E) F) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal
        (4 * (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * D *
          (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ)))) ^ (Q : ℝ) := by
  have hQR1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQR0 : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le zero_lt_one hQR1
  have hdim0 : 0 ≤ (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  set U : ℝ := ∫ y, Y y ∂P with hU
  have hU0 : 0 ≤ U := by
    rw [hU]
    exact le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  have hU2 : U ≤ 2 := by
    have hnorm := le_trans (ofReal_integral_le_lqNorm hY hQR1)
      (lqNorm_le_two hQR1 hw hY)
    have hof : ENNReal.ofReal U ≤ ENNReal.ofReal 2 := by
      simpa only [hU, show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by norm_num] using hnorm
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hof
  set c : ℝ := (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * D *
    (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ))) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    positivity
  have hcell : ∀ i ∈ s, ∀ x,
      (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
          schattenSize (Q : ℝ)
            (blockScale (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) E) F ≤
        c * |Y x - U| := by
    intro i hi x
    have hz0 : 0 ≤ (3 : ℝ) ^ (jStar - lev i) := zpow_nonneg (by norm_num) _
    have hscalar :
        |A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)| =
          A * (3 : ℝ) ^ (jStar - lev i) * |Y x - U| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg hz0]
    have hsize := PortableHistory.schattenSize_le_blockSize
      (isSymmetricBlockMat_blockScale
        (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) hE)
      hF hFpd hQR0
    have hblock := blockSize_blockScale_le_abs_mul hE hF hFpd
      (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U))
    have hsizeD : schattenSize (Q : ℝ)
          (blockScale (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) E) F ≤
        (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ *
          (D * (3 : ℝ) ^ (jStar - lev i) * |Y x - U|) := by
      calc schattenSize (Q : ℝ)
            (blockScale (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) E) F
          ≤ (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ *
              blockSize
                (blockScale (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) E) F :=
            hsize
        _ ≤ (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ *
              (|A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)| * blockSize E F) :=
            mul_le_mul_of_nonneg_left hblock hdim0
        _ = (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ *
              ((A * blockSize E F) * (3 : ℝ) ^ (jStar - lev i) * |Y x - U|) := by
            rw [hscalar]
            ring
        _ ≤ (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ *
              (D * (3 : ℝ) ^ (jStar - lev i) * |Y x - U|) := by
            gcongr
    have hzEq : (3 : ℝ) ^ (jStar - lev i) =
        (3 : ℝ) ^ ((jStar : ℝ) - (lev i : ℝ)) := by
      rw [← Real.rpow_intCast]
      push_cast
      ring
    have hrate :
        (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (jStar - lev i) ≤
          (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ))) := by
      rw [hzEq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hj0 : 0 ≤ (lev i : ℝ) - (jStar : ℝ) := by
        exact_mod_cast sub_nonneg.mpr (hlev i hi)
      have hprod : 0 ≤ (1 - rhoMax) * ((lev i : ℝ) - (jStar : ℝ)) :=
        mul_nonneg (by linarith only [hrho]) hj0
      linarith only [hprod]
    calc (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
          schattenSize (Q : ℝ)
            (blockScale (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) E) F
        ≤ (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
            ((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ *
              (D * (3 : ℝ) ^ (jStar - lev i) * |Y x - U|)) :=
          mul_le_mul_of_nonneg_left hsizeD (Real.rpow_nonneg (by norm_num) _)
      _ = ((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * D) *
            ((3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
              (3 : ℝ) ^ (jStar - lev i)) * |Y x - U| := by ring
      _ ≤ ((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * D) *
            (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ))) * |Y x - U| := by
          gcongr
      _ = c * |Y x - U| := by rw [hc]
  let X : CoeffSpace d → ℝ≥0∞ := fun x => ENNReal.ofReal (s.sup' hs fun i =>
    (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
      schattenSize (Q : ℝ)
        (blockScale (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) E) F)
  have hsup : ∀ x, (s.sup' hs fun i =>
      (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
        schattenSize (Q : ℝ)
          (blockScale (A * (3 : ℝ) ^ (jStar - lev i) * (Y x - U)) E) F) ≤
      c * |Y x - U| := by
    intro x
    exact Finset.sup'_le _ _ fun i hi => hcell i hi x
  have hXbound : ∀ᵐ x ∂P, X x ≤ ENNReal.ofReal (c * (Y x + U)) := by
    filter_upwards [] with x
    refine ENNReal.ofReal_le_ofReal ((hsup x).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hc0
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg
      (le_trans zero_le_one (hY.one_le x)), abs_of_nonneg hU0] using
        abs_sub_le (Y x) 0 U
  have hXLp := eLpNorm_le_of_ae_le_mul_add hY hc0 hQR1 hXbound
  have hXLp4 : eLpNorm X (ENNReal.ofReal (Q : ℝ)) P ≤ ENNReal.ofReal (4 * c) := by
    calc eLpNorm X (ENNReal.ofReal (Q : ℝ)) P
        ≤ ENNReal.ofReal (2 * c) * lqNorm P (Q : ℝ) Y := hXLp
      _ ≤ ENNReal.ofReal (2 * c) * (2 : ℝ≥0∞) :=
        mul_le_mul' le_rfl (lqNorm_le_two hQR1 hw hY)
      _ = ENNReal.ofReal (4 * c) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hc0)]
        congr 1
        ring
  have hp0 : ENNReal.ofReal (Q : ℝ) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hQR0
  have hmoment : eLpNorm X (ENNReal.ofReal (Q : ℝ)) P ^ (Q : ℝ) =
      ∫⁻ x, X x ^ (Q : ℝ) ∂P := by
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hQR0.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hQR0.ne', ENNReal.rpow_one]
    exact lintegral_congr fun x => by rw [enorm_eq_self]
  have hfinal : ∫⁻ x, X x ^ (Q : ℝ) ∂P ≤ ENNReal.ofReal (4 * c) ^ (Q : ℝ) := by
    rw [← hmoment]
    exact ENNReal.rpow_le_rpow hXLp4 hQR0.le
  simpa only [X, c, U, mul_assoc] using hfinal

/-- The coefficient left by the shared below-start maximum is absorbed by the
transported source remainder. -/
theorem below_start_coefficient_absorbed
    {D Lam Cd g Q a rhoMax : ℝ} (hQ : 1 ≤ Q) (hL : 1 ≤ Lam)
    (hD0 : 0 ≤ D) (E : BlockMat d) {jStar : ℤ} (mu mu' : Mat d) {n : ℤ}
    (hCd : 0 ≤ Cd) (hg : g < 1)
    (hD : D ≤ Lam * transportSrcCoeff Cd g E jStar mu mu')
    (hjn : jStar ≤ n) (haQrho : a ≤ Q * rhoMax) :
    (4 * (2 * (d : ℝ)) ^ Q⁻¹ * D *
        (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ)))) ^ Q ≤
      (4 * (2 * (d : ℝ)) ^ Q⁻¹) ^ Q * Lam ^ Q *
        transportSrcRemainder Cd g Q a E jStar mu mu' n := by
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hs0 : 0 ≤ (n : ℝ) - (jStar : ℝ) := by exact_mod_cast sub_nonneg.mpr hjn
  have hK0 : 0 ≤ 4 * (2 * (d : ℝ)) ^ Q⁻¹ := by positivity
  have hrate0 : 0 ≤ (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hrate :
      ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ)))) ^ Q ≤
        (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hmul := mul_le_mul_of_nonneg_right haQrho hs0
    linarith only [hmul]
  have hrem := srcRemainder_absorbed (a := a) hQ hL hD0 E mu mu' n hCd hg hD
  calc (4 * (2 * (d : ℝ)) ^ Q⁻¹ * D *
          (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ)))) ^ Q
      = (4 * (2 * (d : ℝ)) ^ Q⁻¹) ^ Q * D ^ Q *
          ((3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ)))) ^ Q := by
        rw [Real.mul_rpow (mul_nonneg hK0 hD0) hrate0,
          Real.mul_rpow hK0 hD0]
    _ ≤ (4 * (2 * (d : ℝ)) ^ Q⁻¹) ^ Q * D ^ Q *
          (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) := by
        gcongr
    _ ≤ (4 * (2 * (d : ℝ)) ^ Q⁻¹) ^ Q *
          ((D + D ^ Q) *
            (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) := by
        have hDpow : D ^ Q ≤ D + D ^ Q := by linarith only [hD0]
        have hratea0 : 0 ≤ (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) :=
          Real.rpow_nonneg (by norm_num) _
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hDpow hratea0)
          (Real.rpow_nonneg hK0 Q)
    _ ≤ (4 * (2 * (d : ℝ)) ^ Q⁻¹) ^ Q *
          (Lam ^ Q * transportSrcRemainder Cd g Q a E jStar mu mu' n) :=
        mul_le_mul_of_nonneg_left hrem (Real.rpow_nonneg hK0 Q)
    _ = (4 * (2 * (d : ℝ)) ^ Q⁻¹) ^ Q * Lam ^ Q *
          transportSrcRemainder Cd g Q a E jStar mu mu' n := by ring

end


end Transport
end HighContrast
end Homogenization
