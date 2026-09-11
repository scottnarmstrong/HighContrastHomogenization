/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.Amortization
import HCPoly.Provider.ShortHop.BootstrapThresholds

/-!
# The source remainders below the source allowance

This is the last step of `e.global.selection.eccentricity`: the amortized
bounds on the two bridge remainders collapse under the strict hop-length
requirement and the entry-scale clause, and the cutoff coefficient — chosen
before the law against the same structural constant — puts what survives below
the source allowance, uniformly in the reference aspect ratio.

Nothing new is proved here.  The amortized bounds are the previous file's, the
collapse and the uniform choice are the two steps the ordered choice already
carries, and the structural constant that the collapse reads is the one the
amortization exhibits.  What the two statements below add is that the three
numbers the successful short test compares to the source allowance are exactly
those the collapse applies to.

The reference-ratio bound `κ_𝐄 ≤ 6Π` of the factor-six reference-block
comparison is carried as a hypothesis throughout, as it is in the amortization.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- **The comparison remainder is below the source allowance.** -/
theorem bridgeCmpRemainder_le_tauSrc [NeZero d]
    {C Cd g Khop Pi rhoDr chop tauSrc B : ℝ} {E : BlockMat d} {jStar r0 v l0 : ℤ} {k : ℕ}
    {mq mq' : Mat d} (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hg : g < 1) (hrho : 0 < rhoDr)
    (hchop : 0 ≤ chop) (hmq : mq.PosDef) (hmq' : mq'.PosDef) (hPi : 1 ≤ Pi)
    (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mq) (roundedGrid jStar mq') ≤ Khop)
    (hK' : gridRatio (roundedGrid jStar mq') (roundedGrid jStar mq) ≤ Khop)
    (hpre : projDist 1 mq ≤ ((k : ℝ) + 1) * chop)
    (hpre' : projDist 1 mq' ≤ ((k : ℝ) + 1) * chop) (hjv : jStar ≤ v)
    (hscale : (r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ) ≤ (v : ℝ) - (jStar : ℝ))
    (hentry : B * Real.logb 3 (2 + Pi) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hstrict : 2 * chop < rhoDr * (l0 : ℝ) * Real.log 3 / 2)
    (hunif : C * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
          (1 + 2 / (rhoDr * Real.log 3)) *
          Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
        (2 + Pi) ^ (1 - rhoDr * B / 2) ≤ tauSrc) :
    bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' v ≤ tauSrc := by
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hKhop : (0 : ℝ) ≤ Khop := le_trans (le_trans zero_le_one (Transport.one_le_gridRatio _ _)) hK
  have hchi : (0 : ℝ) < chiG g := zero_lt_chiG hg
  have hCr : (0 : ℝ) < 1 + 2 / (rhoDr * Real.log 3) := by
    have hdiv := div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hrho hL)
    linarith only [hdiv]
  have hM0 : (0 : ℝ) ≤ 1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have h2 : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have hKc := mul_nonneg hKhop hchi.le
      linarith only [hKc]
    have hprod := mul_nonneg (mul_nonneg (by linarith only [hCd] : (0 : ℝ) ≤ 24 * Cd)
      (sq_nonneg (Cd * zetaG g))) h2
    linarith only [hprod]
  have hconst : (0 : ℝ) ≤
      C * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
          (1 + 2 / (rhoDr * Real.log 3)) *
        Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hM0) hCr.le) (Real.exp_pos _).le
  refine le_trans (amortized_le_rpow (B := B) (k := k) hrho hPi hconst hentry hstrict ?_) hunif
  exact bridgeCmpRemainder_amortized hC hCd hg hrho hchop hmq hmq' hPi hkap hK hK'
    hpre hpre' hjv hscale

/-- **The shifted remainder is below the source allowance.** -/
theorem bridgeShiftedRemainder_le_tauSrc [NeZero d]
    {C Cd g Khop Pi rhoDr chop tauSrc B : ℝ} {E : BlockMat d} {jStar r0 v l0 l : ℤ} {k : ℕ}
    {mq mq' : Mat d} (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hg : g < 1) (hrho : 0 < rhoDr)
    (hchop : 0 ≤ chop) (hmq : mq.PosDef) (hmq' : mq'.PosDef) (hPi : 1 ≤ Pi)
    (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mq) (roundedGrid jStar mq') ≤ Khop)
    (hK' : gridRatio (roundedGrid jStar mq') (roundedGrid jStar mq) ≤ Khop)
    (hpre : projDist 1 mq ≤ ((k : ℝ) + 1) * chop)
    (hpre' : projDist 1 mq' ≤ ((k : ℝ) + 1) * chop) (hjv : jStar ≤ v)
    (hscale : (r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ) ≤ (v : ℝ) - (jStar : ℝ))
    (hentry : B * Real.logb 3 (2 + Pi) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hstrict : 2 * chop < rhoDr * (l0 : ℝ) * Real.log 3 / 2)
    (hunif : (3 : ℝ) ^ (rhoDr * (l : ℝ)) * C *
            (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
            (1 + 2 / (rhoDr * Real.log 3)) *
            Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
          (2 + Pi) ^ (1 - rhoDr * B / 2) ≤ tauSrc) :
    bridgeShiftedRemainder C Cd g rhoDr E jStar mq mq' v l ≤ tauSrc := by
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hKhop : (0 : ℝ) ≤ Khop := le_trans (le_trans zero_le_one (Transport.one_le_gridRatio _ _)) hK
  have hchi : (0 : ℝ) < chiG g := zero_lt_chiG hg
  have hCr : (0 : ℝ) < 1 + 2 / (rhoDr * Real.log 3) := by
    have hdiv := div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hrho hL)
    linarith only [hdiv]
  have hM0 : (0 : ℝ) ≤ 1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have h2 : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have hKc := mul_nonneg hKhop hchi.le
      linarith only [hKc]
    have hprod := mul_nonneg (mul_nonneg (by linarith only [hCd] : (0 : ℝ) ≤ 24 * Cd)
      (sq_nonneg (Cd * zetaG g))) h2
    linarith only [hprod]
  have hconst : (0 : ℝ) ≤
      (3 : ℝ) ^ (rhoDr * (l : ℝ)) * C *
            (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
            (1 + 2 / (rhoDr * Real.log 3)) *
        Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) hM0) hCr.le)
      (Real.exp_pos _).le
  refine le_trans (amortized_le_rpow (B := B) (k := k) hrho hPi hconst hentry hstrict ?_) hunif
  exact bridgeShiftedRemainder_amortized hC hCd hg hrho hchop hmq hmq' hPi hkap hK hK'
    hpre hpre' hjv hscale

end

end ShortHop
end HighContrast
end Homogenization
