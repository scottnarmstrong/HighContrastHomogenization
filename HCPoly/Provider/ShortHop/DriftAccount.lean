/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.TraceGap
import HCPoly.Provider.Recurrence.PositiveGapClosure
import HCPoly.Setup.TransportObjects

/-!
# The drift account of the short test

Two facts about the linear drift `D_{q,b}(T)` are used by the successful short
test of `p.successful.short.bridge`, and both are consequences of the
monotonicity of the annealed blocks in the generation alone.

The first is that the drift is nonnegative: each increment `G_r = E_{r-1} - E_r`
of the mean order is positive semidefinite, the terminal mean is positive
definite, and the trace of a product of two positive semidefinite matrices is
nonnegative, so every term of the sum is.

The second is the comparison of the two-grid errors
`e.successful.short.preliminary.comparison` with the envelopes of the ordered
choice: replacing the cross-grid factor by the rounded-hop constant, the drift
by its envelope, and the comparison remainder by the source allowance turns each
error into the corresponding envelope.  The lower error carries the only
subtlety, since its coefficient has the cross-grid factor in the denominator as
well; the second constants requirement keeps that denominator above one half for
both values, and the quotient is then monotone.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The drift is nonnegative -/

/-- **The linear drift is nonnegative.**  Under the mean order every increment
is positive semidefinite, and its trace against the inverse of the terminal
mean is therefore nonnegative. -/
theorem linearDrift_nonneg {P : Measure (CoeffSpace d)} {rhoDr : ℝ} {q : Mat d} {b T : ℤ}
    (hT : (toFullBlockMat (adaptedMean P q T)).PosDef)
    (hmono : ∀ r : ℤ, b + 1 ≤ r → r ≤ T →
      toFullBlockMat (adaptedMean P q r) ≤ toFullBlockMat (adaptedMean P q (r - 1))) :
    0 ≤ linearDrift P rhoDr q b T := by
  refine Finset.sum_nonneg fun r hr => ?_
  rw [Finset.mem_Icc] at hr
  have hpsd : (toFullBlockMat (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r))).PosSemidef := by
    rw [Recurrence.toFullBlockMat_blockSub]
    exact Matrix.le_iff.mp (hmono r hr.1 hr.2)
  have htr : 0 ≤ blockTrace (ofFullBlockMat
      ((toFullBlockMat (adaptedMean P q T))⁻¹ *
        toFullBlockMat (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r)))) := by
    rw [blockTrace, toFullBlockMat_ofFullBlockMat]
    exact PortableHistory.trace_mul_nonneg hT.inv.posSemidef hpsd
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * ((T : ℝ) - (r : ℝ))) := by positivity
  exact mul_nonneg h3.le htr

/-! ## The two comparison errors are nonnegative -/

/-- The upper comparison error is nonnegative once the drift and the comparison
remainder are. -/
theorem bridgeErrUpper_nonneg {C Cd g rhoDr K : ℝ} {P : Measure (CoeffSpace d)}
    {E : BlockMat d} {jStar : ℤ} {mq mq' : Mat d} {n l : ℤ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDnn : 0 ≤ linearDrift P rhoDr (roundedGrid jStar mq) jStar n)
    (hRnn : 0 ≤ bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' n) :
    0 ≤ bridgeErrUpper C Cd g rhoDr K P E jStar mq mq' n l := by
  have h1 : (0 : ℝ) < (3 : ℝ) ^ (-(l : ℝ)) := by positivity
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) := by positivity
  have hbr : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
      linearDrift P rhoDr (roundedGrid jStar mq) jStar n := by
    have := mul_nonneg h2.le hDnn
    linarith only [h1, this]
  simpa only [bridgeErrUpper] using
    add_nonneg (mul_nonneg (mul_nonneg hC hK) hbr) hRnn

/-- The lower comparison error is nonnegative once the drift, the comparison
remainder and the denominator are. -/
theorem bridgeErrLower_nonneg {C Cd g rhoDr K : ℝ} {P : Measure (CoeffSpace d)}
    {E : BlockMat d} {jStar : ℤ} {mq mq' : Mat d} {n l : ℤ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hden : C * K * (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2)
    (hDnn : 0 ≤ linearDrift P rhoDr (roundedGrid jStar mq) jStar (n + l))
    (hRnn : 0 ≤ bridgeCmpRemainder C Cd g rhoDr E jStar mq' mq (n + l)) :
    0 ≤ bridgeErrLower C Cd g rhoDr K P E jStar mq mq' n l := by
  have h1 : (0 : ℝ) < (3 : ℝ) ^ (-(l : ℝ)) := by positivity
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) := by positivity
  have hcoef : 0 ≤ C * K / (1 - C * K * (3 : ℝ) ^ (-(l : ℝ))) :=
    div_nonneg (mul_nonneg hC hK) (by linarith only [hden])
  have hbr : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
      linearDrift P rhoDr (roundedGrid jStar mq) jStar (n + l) := by
    have := mul_nonneg h2.le hDnn
    linarith only [h1, this]
  simpa only [bridgeErrLower] using add_nonneg (mul_nonneg hcoef hbr) hRnn

/-! ## The two comparison errors sit below the envelopes -/

/-- **The upper comparison error sits below the upper envelope.**  The
cross-grid factor is replaced by the rounded-hop constant, the drift at the
intermediate scale by its envelope, and the comparison remainder by the source
allowance. -/
theorem bridgeErrUpper_le_shortErrUpper {C Cd g rhoDr K Khop b delta R1 : ℝ}
    {P : Measure (CoeffSpace d)} {E : BlockMat d} {jStar : ℤ} {mq mq' : Mat d} {n l : ℤ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKKhop : K ≤ Khop)
    (hDnn : 0 ≤ linearDrift P rhoDr (roundedGrid jStar mq) jStar n)
    (hDle : linearDrift P rhoDr (roundedGrid jStar mq) jStar n ≤
      shortDriftNew d rhoDr l b delta)
    (hR : bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' n ≤ R1) :
    bridgeErrUpper C Cd g rhoDr K P E jStar mq mq' n l ≤
      shortErrUpper d C Khop rhoDr l b delta R1 := by
  have h1 : (0 : ℝ) < (3 : ℝ) ^ (-(l : ℝ)) := by positivity
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) := by positivity
  have hbr0 : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
      linearDrift P rhoDr (roundedGrid jStar mq) jStar n := by
    have := mul_nonneg h2.le hDnn
    linarith only [h1, this]
  have hbr : (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
        linearDrift P rhoDr (roundedGrid jStar mq) jStar n ≤
      (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
        shortDriftNew d rhoDr l b delta := by
    linarith only [mul_le_mul_of_nonneg_left hDle h2.le]
  have hcoef : C * K ≤ C * Khop := mul_le_mul_of_nonneg_left hKKhop hC
  have hmain := mul_le_mul hcoef hbr hbr0 (le_trans (mul_nonneg hC hK) hcoef)
  simpa only [bridgeErrUpper, shortErrUpper] using add_le_add hmain hR

/-- **The lower comparison error sits below the lower envelope.**  The same
three replacements, with the cross-grid factor also entering the denominator of
the coefficient; the second constants requirement keeps that denominator above
one half at the rounded-hop constant, hence at the cross-grid factor too. -/
theorem bridgeErrLower_le_shortErrLower {C Cd g rhoDr K Khop b delta R2 : ℝ}
    {P : Measure (CoeffSpace d)} {E : BlockMat d} {jStar : ℤ} {mq mq' : Mat d} {n l : ℤ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKKhop : K ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2)
    (hDnn : 0 ≤ linearDrift P rhoDr (roundedGrid jStar mq) jStar (n + l))
    (hDle : linearDrift P rhoDr (roundedGrid jStar mq) jStar (n + l) ≤
      shortDriftTerm d rhoDr l b delta)
    (hR : bridgeCmpRemainder C Cd g rhoDr E jStar mq' mq (n + l) ≤ R2) :
    bridgeErrLower C Cd g rhoDr K P E jStar mq mq' n l ≤
      shortErrLower d C Khop rhoDr l b delta R2 := by
  have h1 : (0 : ℝ) < (3 : ℝ) ^ (-(l : ℝ)) := by positivity
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) := by positivity
  have hKden : C * K * (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKKhop hC) h1.le) hden
  have hposK : (0 : ℝ) < 1 - C * K * (3 : ℝ) ^ (-(l : ℝ)) := by linarith only [hKden]
  have hposKhop : (0 : ℝ) < 1 - C * Khop * (3 : ℝ) ^ (-(l : ℝ)) := by linarith only [hden]
  have hdenle : 1 - C * Khop * (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 - C * K * (3 : ℝ) ^ (-(l : ℝ)) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKKhop hC) h1.le
    linarith only [this]
  have hcoef : C * K / (1 - C * K * (3 : ℝ) ^ (-(l : ℝ))) ≤
      C * Khop / (1 - C * Khop * (3 : ℝ) ^ (-(l : ℝ))) :=
    div_le_div₀ (le_trans (mul_nonneg hC hK) (mul_le_mul_of_nonneg_left hKKhop hC))
      (mul_le_mul_of_nonneg_left hKKhop hC) hposKhop hdenle
  have hcoef0 : 0 ≤ C * K / (1 - C * K * (3 : ℝ) ^ (-(l : ℝ))) :=
    div_nonneg (mul_nonneg hC hK) hposK.le
  have hbr0 : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
      linearDrift P rhoDr (roundedGrid jStar mq) jStar (n + l) := by
    have := mul_nonneg h2.le hDnn
    linarith only [h1, this]
  have hbr : (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
        linearDrift P rhoDr (roundedGrid jStar mq) jStar (n + l) ≤
      (3 : ℝ) ^ (-(l : ℝ)) + (3 : ℝ) ^ (-(1 - rhoDr) * (l : ℝ)) *
        shortDriftTerm d rhoDr l b delta := by
    linarith only [mul_le_mul_of_nonneg_left hDle h2.le]
  have hmain := mul_le_mul hcoef hbr hbr0 (le_trans hcoef0 hcoef)
  simpa only [bridgeErrLower, shortErrLower] using add_le_add hmain hR

/-- **The new-grid drift envelope dominates the shifted-drift right-hand
side.**  The cross-grid factor is replaced by the rounded-hop constant, the
lower comparison error by its envelope, the drift at the terminal scale by its
envelope, and the shifted remainder by the source allowance. -/
theorem shifted_le_shortNewDrift {C Khop rhoDr K epsMinus b delta R2 R3 D : ℝ}
    {l : ℤ} {Rsh : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKKhop : K ≤ Khop)
    (hDnn : 0 ≤ D) (hDle : D ≤ shortDriftTerm d rhoDr l b delta)
    (hem : epsMinus ≤ shortErrLower d C Khop rhoDr l b delta R2)
    (hRsh : Rsh ≤ R3) :
    C * (epsMinus + K * (3 : ℝ) ^ (-(l : ℝ)) +
        (1 + K) * (3 : ℝ) ^ (2 * rhoDr * (l : ℝ)) * D + Rsh) ≤
      shortNewDrift d C Khop rhoDr l b delta R2 R3 := by
  have h1 : (0 : ℝ) < (3 : ℝ) ^ (-(l : ℝ)) := by positivity
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (2 * rhoDr * (l : ℝ)) := by positivity
  have hKle : K * (3 : ℝ) ^ (-(l : ℝ)) ≤ Khop * (3 : ℝ) ^ (-(l : ℝ)) :=
    mul_le_mul_of_nonneg_right hKKhop h1.le
  have hterm : (1 + K) * (3 : ℝ) ^ (2 * rhoDr * (l : ℝ)) * D ≤
      (1 + Khop) * (3 : ℝ) ^ (2 * rhoDr * (l : ℝ)) * shortDriftTerm d rhoDr l b delta := by
    refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith only [hKKhop]) h2.le) hDle hDnn ?_
    have : (0 : ℝ) ≤ 1 + Khop := by linarith only [hK, hKKhop]
    positivity
  simpa only [shortNewDrift] using
    mul_le_mul_of_nonneg_left (by linarith only [hem, hKle, hterm, hRsh]) hC

end

end ShortHop
end HighContrast
end Homogenization
