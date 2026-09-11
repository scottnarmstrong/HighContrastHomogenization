/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.Eccentricity
import HCPoly.Provider.Transport.CoefficientArithmetic
import HCPoly.Provider.Transport.TransportCoefficients
import HCPoly.Provider.Transport.WhitneySquareWeights
import HCPoly.Setup.TransportObjects

/-!
# The bridge source coefficient and its two remainders

The source coefficient `𝖣_src^{br,S}(q,q')` of the two-grid comparison in
`p.successful.short.bridge` is one plus a maximum of four sums of a continued
and an early coefficient, and the two remainders -- the source remainder of that
comparison and `e.two.grid.drift.source.convolution` -- multiply it by the
two-grid constant, a linear factor in the scale and a geometric weight.

Two facts about them are proved here.

*They are nonnegative.*  Every factor of the two coefficients is nonnegative —
the cross-grid factor is at least one, the reference ratio is an infimum of
nonnegative numbers, the boundary constant is a nonnegative multiple of a square
root, and the two geometric series are positive below the critical exponent — so
the source coefficient is at least one and both remainders are nonnegative at or
above the alignment scale.  This is what the successful short test reads as the
lower half of its source hypotheses.

*They are bounded by the printed bootstrap coefficient.*  If both witnesses lie
within projective distance `t` of the identity their boundary constants are at
most `C_de^tζ_g`, the cross-grid factors are at most the rounded-hop constant,
and the reference ratio is at most `6Π`; the four entries of the maximum then
share one bound, and collecting the constants gives
`𝖣_src^{br,S}(q,q') ≤ C_{d,g,K_hop}(2+Π)e^{2t}` with the structural constant
exhibited.  At `t = (k+1)c_hop` along a prefix of projective hops this is the
printed bootstrap coefficient, and the bound is symmetric in the two witnesses,
so the same statement serves the reversed pair.  The reference-ratio bound is the
one input taken as a hypothesis: it is the factor-six reference-block comparison,
which belongs to the reference geometry and not to this proof.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The scalar factors -/

/-- The reference ratio is nonnegative: it is an infimum of nonnegative
numbers. -/
theorem zero_le_kappaRef (E : BlockMat d) : 0 ≤ kappaRef E := by
  exact Transport.zero_le_kappaRef E

/-- The geometric series `χ_g = (3^{1-g} - 1)^{-1}` is positive below the
critical exponent. -/
theorem zero_lt_chiG {g : ℝ} (hg : g < 1) : 0 < chiG g := by
  exact Transport.zero_lt_chiG hg

/-! ## Nonnegativity of the two bridge coefficients -/

/-- The continued bridge coefficient is nonnegative. -/
theorem zero_le_bridgeContCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1) (E : BlockMat d)
    (jStar : ℤ) (mp mv mr : Mat d) : 0 ≤ bridgeContCoeff Cd g E jStar mp mv mr := by
  have hG : (0 : ℝ) ≤ gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) :=
    le_trans zero_le_one (Transport.one_le_gridRatio _ _)
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg hCd hG) (zero_le_kappaRef E)) (Transport.zero_le_boundaryConst hCd hg mp))
    (Transport.zero_le_boundaryConst hCd hg mr)) (zero_lt_chiG hg).le) (by norm_num)

/-- The early bridge coefficient is nonnegative. -/
theorem zero_le_bridgeEarlyCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1) (E : BlockMat d)
    (mv mr : Mat d) : 0 ≤ bridgeEarlyCoeff Cd g E mv mr :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCd (zero_le_kappaRef E))
    (Transport.zero_le_boundaryConst hCd hg mv)) (Transport.zero_le_boundaryConst hCd hg mr))
    (by norm_num)

/-- **The source coefficient is at least one.** -/
theorem one_le_bridgeSrcCoeff {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1) (E : BlockMat d)
    (jStar : ℤ) (mq mq' : Mat d) : 1 ≤ bridgeSrcCoeff Cd g E jStar mq mq' := by
  have h : (0 : ℝ) ≤ bridgeContCoeff Cd g E jStar mq mq' mq + bridgeEarlyCoeff Cd g E mq' mq :=
    add_nonneg (zero_le_bridgeContCoeff hCd hg E jStar mq mq' mq)
      (zero_le_bridgeEarlyCoeff hCd hg E mq' mq)
  rw [bridgeSrcCoeff]
  have hmax := le_trans (le_trans h (le_max_left _
      (bridgeContCoeff Cd g E jStar mq mq' mq' + bridgeEarlyCoeff Cd g E mq' mq')))
    (le_max_left _ (max (bridgeContCoeff Cd g E jStar mq' mq mq + bridgeEarlyCoeff Cd g E mq mq)
      (bridgeContCoeff Cd g E jStar mq' mq mq' + bridgeEarlyCoeff Cd g E mq mq')))
  linarith only [hmax]

/-! ## Nonnegativity of the two remainders -/

/-- **The comparison remainder is nonnegative** at or above the alignment
scale. -/
theorem zero_le_bridgeCmpRemainder {C Cd g rhoDr : ℝ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd)
    (hg : g < 1) (E : BlockMat d) {jStar v : ℤ} (hv : jStar ≤ v) (mq mq' : Mat d) :
    0 ≤ bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' v := by
  have hlin : (0 : ℝ) ≤ 1 + ((v : ℝ) - (jStar : ℝ)) := by
    have : (jStar : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    linarith only [this]
  have hsrc : (0 : ℝ) ≤ bridgeSrcCoeff Cd g E jStar mq mq' :=
    le_trans zero_le_one (one_le_bridgeSrcCoeff hCd hg E jStar mq mq')
  have hgeo : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (jStar : ℝ))) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg hC hsrc) hlin) hgeo.le

/-- **The shifted remainder is nonnegative** at or above the alignment scale. -/
theorem zero_le_bridgeShiftedRemainder {C Cd g rhoDr : ℝ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd)
    (hg : g < 1) (E : BlockMat d) {jStar n : ℤ} (hn : jStar ≤ n) (mq mq' : Mat d) (l : ℤ) :
    0 ≤ bridgeShiftedRemainder C Cd g rhoDr E jStar mq mq' n l := by
  have hlin : (0 : ℝ) ≤ 1 + ((n : ℝ) - (jStar : ℝ)) := by
    have : (jStar : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith only [this]
  have hsrc : (0 : ℝ) ≤ bridgeSrcCoeff Cd g E jStar mq mq' :=
    le_trans zero_le_one (one_le_bridgeSrcCoeff hCd hg E jStar mq mq')
  have hshift : (0 : ℝ) < (3 : ℝ) ^ (rhoDr * (l : ℝ)) := by positivity
  have hgeo : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * ((n : ℝ) - (jStar : ℝ))) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hsrc) hshift.le) hlin) hgeo.le

/-! ## The bootstrap bound on the source coefficient -/

/-- **The bootstrap bound on the source coefficient**
(`e.global.selection.eccentricity`, the bridge half), with the
structural constant exhibited.  The reference-ratio bound `κ_𝐄 ≤ 6Π` of the
factor-six reference-block comparison belongs to the reference geometry, not to
this proof, and is carried as a hypothesis. -/
theorem bridgeSrcCoeff_le [NeZero d] {Cd g Khop Pi t : ℝ} {E : BlockMat d} {jStar : ℤ}
    {mq mq' : Mat d} (hCd : 0 ≤ Cd) (hg : g < 1) (ht : 0 ≤ t)
    (hmq : mq.PosDef) (hmq' : mq'.PosDef) (hPi : 1 ≤ Pi) (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mq) (roundedGrid jStar mq') ≤ Khop)
    (hK' : gridRatio (roundedGrid jStar mq') (roundedGrid jStar mq) ≤ Khop)
    (hpre : projDist 1 mq ≤ t) (hpre' : projDist 1 mq' ≤ t) :
    bridgeSrcCoeff Cd g E jStar mq mq' ≤
      (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) * (2 + Pi) *
        Real.exp (2 * t) := by
  have hKhop : (0 : ℝ) ≤ Khop := le_trans (le_trans zero_le_one (Transport.one_le_gridRatio _ _)) hK
  have hchi : 0 < chiG g := zero_lt_chiG hg
  have hzeta : 0 < zetaG g := Transport.zero_lt_zetaG hg
  have hkap0 : (0 : ℝ) ≤ kappaRef E := zero_le_kappaRef E
  have hPi0 : (0 : ℝ) ≤ 6 * Pi := by linarith only [hPi]
  obtain ⟨beta, hbeta⟩ : ∃ b : ℝ, b = Cd * Real.exp t * zetaG g := ⟨_, rfl⟩
  have hbeta0 : 0 ≤ beta := by
    rw [hbeta]
    exact mul_nonneg (mul_nonneg hCd (Real.exp_pos _).le) hzeta.le
  have hBq : boundaryConst Cd g mq ≤ beta := by
    rw [hbeta]; exact boundaryConst_le_exp hCd hg hmq hpre
  have hBq' : boundaryConst Cd g mq' ≤ beta := by
    rw [hbeta]; exact boundaryConst_le_exp hCd hg hmq' hpre'
  have hB0 : 0 ≤ boundaryConst Cd g mq := Transport.zero_le_boundaryConst hCd hg mq
  have hB0' : 0 ≤ boundaryConst Cd g mq' := Transport.zero_le_boundaryConst hCd hg mq'
  -- the two coefficients at the bootstrap bounds
  have hcont : ∀ mp mv mr : Mat d,
      gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) ≤ Khop →
      boundaryConst Cd g mp ≤ beta → boundaryConst Cd g mr ≤ beta →
      0 ≤ boundaryConst Cd g mp → 0 ≤ boundaryConst Cd g mr →
      bridgeContCoeff Cd g E jStar mp mv mr ≤
        Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 := by
    intro mp mv mr hKmp hBp hBr hBp0 hBr0
    have hBB : boundaryConst Cd g mp * boundaryConst Cd g mr ≤ beta * beta :=
      mul_le_mul hBp hBr hBr0 hbeta0
    have hkBB : kappaRef E * (boundaryConst Cd g mp * boundaryConst Cd g mr) ≤
        6 * Pi * (beta * beta) := mul_le_mul hkap hBB (mul_nonneg hBp0 hBr0) hPi0
    have hinner : gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
        (kappaRef E * (boundaryConst Cd g mp * boundaryConst Cd g mr)) ≤
        Khop * (6 * Pi * (beta * beta)) :=
      mul_le_mul hKmp hkBB (mul_nonneg hkap0 (mul_nonneg hBp0 hBr0)) hKhop
    have hfront : (0 : ℝ) ≤ Cd * chiG g * 4 :=
      mul_nonneg (mul_nonneg hCd hchi.le) (by norm_num)
    calc bridgeContCoeff Cd g E jStar mp mv mr
        = Cd * chiG g * 4 * (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
            (kappaRef E * (boundaryConst Cd g mp * boundaryConst Cd g mr))) := by
          rw [bridgeContCoeff]; ring
      _ ≤ Cd * chiG g * 4 * (Khop * (6 * Pi * (beta * beta))) :=
          mul_le_mul_of_nonneg_left hinner hfront
      _ = Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 := by ring
  have hearly : ∀ mv mr : Mat d,
      boundaryConst Cd g mv ≤ beta → boundaryConst Cd g mr ≤ beta →
      0 ≤ boundaryConst Cd g mv → 0 ≤ boundaryConst Cd g mr →
      bridgeEarlyCoeff Cd g E mv mr ≤ Cd * (6 * Pi) * beta * beta * 4 := by
    intro mv mr hBv hBr hBv0 hBr0
    have hBB : boundaryConst Cd g mv * boundaryConst Cd g mr ≤ beta * beta :=
      mul_le_mul hBv hBr hBr0 hbeta0
    have hkBB : kappaRef E * (boundaryConst Cd g mv * boundaryConst Cd g mr) ≤
        6 * Pi * (beta * beta) := mul_le_mul hkap hBB (mul_nonneg hBv0 hBr0) hPi0
    have hfront : (0 : ℝ) ≤ Cd * 4 := mul_nonneg hCd (by norm_num)
    calc bridgeEarlyCoeff Cd g E mv mr
        = Cd * 4 * (kappaRef E * (boundaryConst Cd g mv * boundaryConst Cd g mr)) := by
          rw [bridgeEarlyCoeff]; ring
      _ ≤ Cd * 4 * (6 * Pi * (beta * beta)) := mul_le_mul_of_nonneg_left hkBB hfront
      _ = Cd * (6 * Pi) * beta * beta * 4 := by ring
  -- the four entries of the maximum share one bound
  have hbound : ∀ mp mv mr ms : Mat d,
      gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) ≤ Khop →
      boundaryConst Cd g mp ≤ beta → boundaryConst Cd g mr ≤ beta →
      boundaryConst Cd g ms ≤ beta →
      0 ≤ boundaryConst Cd g mp → 0 ≤ boundaryConst Cd g mr →
      0 ≤ boundaryConst Cd g ms →
      bridgeContCoeff Cd g E jStar mp mv mr + bridgeEarlyCoeff Cd g E ms mr ≤
        Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 +
          Cd * (6 * Pi) * beta * beta * 4 :=
    fun mp mv mr ms hKmp hBp hBr hBs hBp0 hBr0 hBs0 =>
      add_le_add (hcont mp mv mr hKmp hBp hBr hBp0 hBr0) (hearly ms mr hBs hBr hBs0 hBr0)
  have hmax : bridgeSrcCoeff Cd g E jStar mq mq' ≤
      1 + (Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 +
        Cd * (6 * Pi) * beta * beta * 4) := by
    rw [bridgeSrcCoeff]
    have hall := max_le
      (max_le (hbound mq mq' mq mq' hK hBq hBq hBq' hB0 hB0 hB0')
        (hbound mq mq' mq' mq' hK hBq hBq' hBq' hB0 hB0' hB0'))
      (max_le (hbound mq' mq mq mq hK' hBq' hBq hBq hB0' hB0 hB0)
        (hbound mq' mq mq' mq hK' hBq' hBq' hBq hB0' hB0' hB0))
    linarith only [hall]
  -- the exponential factor and the collected constant
  have hX1 : (1 : ℝ) ≤ Real.exp (2 * t) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [ht])
  have hexp : Real.exp t * Real.exp t = Real.exp (2 * t) := by
    rw [← Real.exp_add]; ring_nf
  have hsum : Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 +
        Cd * (6 * Pi) * beta * beta * 4 =
      24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) * Pi * Real.exp (2 * t) := by
    rw [← hexp, hbeta]; ring
  have hM0 : (0 : ℝ) ≤ 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have h2 : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have := mul_nonneg hKhop hchi.le
      linarith only [this]
    exact mul_nonneg (mul_nonneg (by linarith only [hCd]) (sq_nonneg _)) h2
  have hfinal := Transport.one_add_mul_le hM0 hPi hX1
  linarith only [hmax, hsum, hfinal]

end

end ShortHop
end HighContrast
end Homogenization
