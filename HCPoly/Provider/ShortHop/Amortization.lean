/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.SourceCoefficient

/-!
# The amortized source remainders

The hop-index bootstrap `e.global.selection.eccentricity` turns the two
bridge remainders into the amortized form that makes them geometrically small
along the sequence of geometry changes: a fixed structural constant times
`(2 + Π)`, times the geometric gain `3^{-ρ_dr(r_0-j_*)/2}` of the entry scale,
times `exp[-k(ρ_dr ℓ₀ log3/2 - 2c_hop)]`.

Three steps do that, and all three are here.

*The linear factor is absorbed.*  The printed sentence "for `β > 0` the quantity
`(1+N)3^{-βN/2}` is bounded on `N ∈ ℤ_{≥0}`" is proved with the explicit constant
`1 + 2/(β log 3)`: writing `b = β log3/2`, the elementary bound `x + 1 ≤ e^x`
gives `N ≤ e^{bN}/b`, and `1 ≤ e^{bN}` gives `1 + N ≤ (1 + 1/b)e^{bN}`, which is
the assertion after multiplying by `e^{-bN}` and by the halved weight.

*The scale gain is split.*  The bootstrap's scale bound
`n_k - j_* ≥ r_0 - j_* + (k+1)ℓ₀` makes the halved geometric weight at most the
product of the weight at the entry scale and the weight at `(k+1)ℓ₀`.

*The exponential and the geometric weight combine.*  The coefficient's factor
`e^{2(k+1)c_hop}` and the weight `3^{-ρ_dr(k+1)ℓ₀/2}` are one exponential
`exp[(k+1)(2c_hop - ρ_dr ℓ₀ log3/2)]`, which is the fixed first-arrival factor
times `exp[-k(ρ_dr ℓ₀ log3/2 - 2c_hop)]`, exactly as the reference text says.

The shifted remainder is the comparison remainder at the same scale times the
fixed factor `3^{ρ_dr ℓ}`, so its amortized bound is the same one with that
factor collected into the constant.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The linear factor against half the geometric weight -/

/-- **The linear factor is absorbed by half the geometric weight**, with the
constant exhibited. -/
theorem one_add_mul_rpow_le {rhoDr N : ℝ} (hrho : 0 < rhoDr) (hN : 0 ≤ N) :
    (1 + N) * (3 : ℝ) ^ (-rhoDr * N) ≤
      (1 + 2 / (rhoDr * Real.log 3)) * (3 : ℝ) ^ (-rhoDr * N / 2) := by
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hrL : rhoDr * Real.log 3 ≠ 0 := ne_of_gt (by positivity)
  have hb : (0 : ℝ) < rhoDr * Real.log 3 / 2 := by positivity
  have hone : (1 : ℝ) ≤ Real.exp (rhoDr * Real.log 3 / 2 * N) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hb.le hN)
  have hlin : rhoDr * Real.log 3 / 2 * N ≤ Real.exp (rhoDr * Real.log 3 / 2 * N) := by
    have h := Real.add_one_le_exp (rhoDr * Real.log 3 / 2 * N)
    linarith only [h]
  have hNle : N ≤ Real.exp (rhoDr * Real.log 3 / 2 * N) / (rhoDr * Real.log 3 / 2) := by
    rw [le_div_iff₀ hb]
    linarith only [hlin]
  have hsplit : (1 + 2 / (rhoDr * Real.log 3)) * Real.exp (rhoDr * Real.log 3 / 2 * N) =
      Real.exp (rhoDr * Real.log 3 / 2 * N) +
        Real.exp (rhoDr * Real.log 3 / 2 * N) / (rhoDr * Real.log 3 / 2) := by
    field_simp
  have hkey : 1 + N ≤
      (1 + 2 / (rhoDr * Real.log 3)) * Real.exp (rhoDr * Real.log 3 / 2 * N) := by
    rw [hsplit]
    linarith only [hone, hNle]
  have hcancel : Real.exp (rhoDr * Real.log 3 / 2 * N) *
      Real.exp (-(rhoDr * Real.log 3 / 2 * N)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hstep : (1 + N) * Real.exp (-(rhoDr * Real.log 3 / 2 * N)) ≤
      1 + 2 / (rhoDr * Real.log 3) := by
    calc (1 + N) * Real.exp (-(rhoDr * Real.log 3 / 2 * N))
        ≤ (1 + 2 / (rhoDr * Real.log 3)) * Real.exp (rhoDr * Real.log 3 / 2 * N) *
            Real.exp (-(rhoDr * Real.log 3 / 2 * N)) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ = 1 + 2 / (rhoDr * Real.log 3) := by rw [mul_assoc, hcancel, mul_one]
  have hpow : (3 : ℝ) ^ (-rhoDr * N) =
      Real.exp (-(rhoDr * Real.log 3 / 2 * N)) * (3 : ℝ) ^ (-rhoDr * N / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    congr 1
    ring
  have hW : (0 : ℝ) ≤ (3 : ℝ) ^ (-rhoDr * N / 2) := by positivity
  rw [hpow]
  calc (1 + N) * (Real.exp (-(rhoDr * Real.log 3 / 2 * N)) * (3 : ℝ) ^ (-rhoDr * N / 2))
      = (1 + N) * Real.exp (-(rhoDr * Real.log 3 / 2 * N)) *
          (3 : ℝ) ^ (-rhoDr * N / 2) := by ring
    _ ≤ (1 + 2 / (rhoDr * Real.log 3)) * (3 : ℝ) ^ (-rhoDr * N / 2) :=
        mul_le_mul_of_nonneg_right hstep hW

/-! ## The shifted remainder against the comparison remainder -/

/-- The shifted remainder is the comparison remainder at the same scale times the
fixed factor `3^{ρ_dr ℓ}`. -/
theorem bridgeShiftedRemainder_eq_mul (C Cd g rhoDr : ℝ) (E : BlockMat d) (jStar : ℤ)
    (mq mq' : Mat d) (n l : ℤ) :
    bridgeShiftedRemainder C Cd g rhoDr E jStar mq mq' n l =
      (3 : ℝ) ^ (rhoDr * (l : ℝ)) * bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' n := by
  rw [bridgeShiftedRemainder, bridgeCmpRemainder]
  ring

/-! ## The amortized bound on the comparison remainder -/

/-- **The amortized comparison remainder**, with the structural constant
exhibited.  This is exactly the hypothesis `amortized_le_rpow` reads. -/
theorem bridgeCmpRemainder_amortized [NeZero d] {C Cd g Khop Pi rhoDr chop : ℝ}
    {E : BlockMat d} {jStar r0 v l0 : ℤ} {k : ℕ} {mq mq' : Mat d}
    (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hg : g < 1) (hrho : 0 < rhoDr) (hchop : 0 ≤ chop)
    (hmq : mq.PosDef) (hmq' : mq'.PosDef) (hPi : 1 ≤ Pi) (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mq) (roundedGrid jStar mq') ≤ Khop)
    (hK' : gridRatio (roundedGrid jStar mq') (roundedGrid jStar mq) ≤ Khop)
    (hpre : projDist 1 mq ≤ ((k : ℝ) + 1) * chop)
    (hpre' : projDist 1 mq' ≤ ((k : ℝ) + 1) * chop) (hjv : jStar ≤ v)
    (hscale : (r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ) ≤ (v : ℝ) - (jStar : ℝ)) :
    bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' v ≤
      C * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
            (1 + 2 / (rhoDr * Real.log 3)) *
            Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
          (2 + Pi) * (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
        Real.exp (-(k : ℝ) * (rhoDr * (l0 : ℝ) * Real.log 3 / 2 - 2 * chop)) := by
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hrL : (0 : ℝ) < rhoDr * Real.log 3 := mul_pos hrho hL
  have hCr : (0 : ℝ) < 1 + 2 / (rhoDr * Real.log 3) := by
    have hdiv := div_pos (by norm_num : (0 : ℝ) < 2) hrL
    linarith only [hdiv]
  have hKhop : (0 : ℝ) ≤ Khop := le_trans (le_trans zero_le_one (Transport.one_le_gridRatio _ _)) hK
  have hchi : (0 : ℝ) < chiG g := zero_lt_chiG hg
  have ht : (0 : ℝ) ≤ ((k : ℝ) + 1) * chop := mul_nonneg (by positivity) hchop
  have hN : (0 : ℝ) ≤ (v : ℝ) - (jStar : ℝ) := by
    have hcast : (jStar : ℝ) ≤ (v : ℝ) := by exact_mod_cast hjv
    linarith only [hcast]
  -- the source coefficient at the bootstrap bound
  have hsrc := bridgeSrcCoeff_le (Khop := Khop) (Pi := Pi) (t := ((k : ℝ) + 1) * chop)
    hCd hg ht hmq hmq' hPi hkap hK hK' hpre hpre'
  have hsrc0 : (0 : ℝ) ≤ bridgeSrcCoeff Cd g E jStar mq mq' :=
    le_trans zero_le_one (one_le_bridgeSrcCoeff hCd hg E jStar mq mq')
  have hM0 : (0 : ℝ) ≤ 1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have h2 : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have hKc := mul_nonneg hKhop hchi.le
      linarith only [hKc]
    have hprod := mul_nonneg (mul_nonneg (by linarith only [hCd] : (0 : ℝ) ≤ 24 * Cd)
      (sq_nonneg (Cd * zetaG g))) h2
    linarith only [hprod]
  -- the linear factor and the geometric weight
  have hlin := one_add_mul_rpow_le (N := (v : ℝ) - (jStar : ℝ)) hrho hN
  have hlin0 : (0 : ℝ) ≤ (1 + ((v : ℝ) - (jStar : ℝ))) *
      (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (jStar : ℝ))) :=
    mul_nonneg (by linarith only [hN]) (by positivity)
  have hgeo : (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (jStar : ℝ)) / 2) ≤
      (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
        (3 : ℝ) ^ (-rhoDr * (((k : ℝ) + 1) * (l0 : ℝ)) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hmul := mul_le_mul_of_nonneg_left hscale hrho.le
    linarith only [hmul]
  -- the two exponentials combine
  have hcomb : Real.exp (2 * (((k : ℝ) + 1) * chop)) *
      (3 : ℝ) ^ (-rhoDr * (((k : ℝ) + 1) * (l0 : ℝ)) / 2) =
      Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
        Real.exp (-(k : ℝ) * (rhoDr * (l0 : ℝ) * Real.log 3 / 2 - 2 * chop)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  -- the assembly
  have hleft : C * bridgeSrcCoeff Cd g E jStar mq mq' ≤
      C * ((1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) * (2 + Pi) *
        Real.exp (2 * (((k : ℝ) + 1) * chop))) := mul_le_mul_of_nonneg_left hsrc hC
  have hleft0 : (0 : ℝ) ≤ C * ((1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
      (2 + Pi) * Real.exp (2 * (((k : ℝ) + 1) * chop))) :=
    mul_nonneg hC (mul_nonneg (mul_nonneg hM0 (by linarith only [hPi]))
      (Real.exp_pos _).le)
  calc bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' v
      = C * bridgeSrcCoeff Cd g E jStar mq mq' *
          ((1 + ((v : ℝ) - (jStar : ℝ))) *
            (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (jStar : ℝ)))) := by
        rw [bridgeCmpRemainder]; ring
    _ ≤ C * ((1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) * (2 + Pi) *
            Real.exp (2 * (((k : ℝ) + 1) * chop))) *
          ((1 + 2 / (rhoDr * Real.log 3)) *
            (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (jStar : ℝ)) / 2)) :=
        mul_le_mul hleft hlin hlin0 hleft0
    _ ≤ C * ((1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) * (2 + Pi) *
            Real.exp (2 * (((k : ℝ) + 1) * chop))) *
          ((1 + 2 / (rhoDr * Real.log 3)) *
            ((3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
              (3 : ℝ) ^ (-rhoDr * (((k : ℝ) + 1) * (l0 : ℝ)) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeo hCr.le) hleft0
    _ = C * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
            (1 + 2 / (rhoDr * Real.log 3)) * (2 + Pi) *
            (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
          (Real.exp (2 * (((k : ℝ) + 1) * chop)) *
            (3 : ℝ) ^ (-rhoDr * (((k : ℝ) + 1) * (l0 : ℝ)) / 2)) := by ring
    _ = C * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
            (1 + 2 / (rhoDr * Real.log 3)) * (2 + Pi) *
            (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
          (Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
            Real.exp (-(k : ℝ) *
              (rhoDr * (l0 : ℝ) * Real.log 3 / 2 - 2 * chop))) := by rw [hcomb]
    _ = C * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
              (1 + 2 / (rhoDr * Real.log 3)) *
              Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
            (2 + Pi) * (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
          Real.exp (-(k : ℝ) *
            (rhoDr * (l0 : ℝ) * Real.log 3 / 2 - 2 * chop)) := by ring

/-- **The amortized shifted remainder**, the same bound with the fixed factor
`3^{ρ_dr ℓ}` collected into the structural constant. -/
theorem bridgeShiftedRemainder_amortized [NeZero d] {C Cd g Khop Pi rhoDr chop : ℝ}
    {E : BlockMat d} {jStar r0 v l0 l : ℤ} {k : ℕ} {mq mq' : Mat d}
    (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hg : g < 1) (hrho : 0 < rhoDr) (hchop : 0 ≤ chop)
    (hmq : mq.PosDef) (hmq' : mq'.PosDef) (hPi : 1 ≤ Pi) (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mq) (roundedGrid jStar mq') ≤ Khop)
    (hK' : gridRatio (roundedGrid jStar mq') (roundedGrid jStar mq) ≤ Khop)
    (hpre : projDist 1 mq ≤ ((k : ℝ) + 1) * chop)
    (hpre' : projDist 1 mq' ≤ ((k : ℝ) + 1) * chop) (hjv : jStar ≤ v)
    (hscale : (r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ) ≤ (v : ℝ) - (jStar : ℝ)) :
    bridgeShiftedRemainder C Cd g rhoDr E jStar mq mq' v l ≤
      (3 : ℝ) ^ (rhoDr * (l : ℝ)) * C *
            (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
            (1 + 2 / (rhoDr * Real.log 3)) *
            Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
          (2 + Pi) * (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
        Real.exp (-(k : ℝ) * (rhoDr * (l0 : ℝ) * Real.log 3 / 2 - 2 * chop)) := by
  rw [bridgeShiftedRemainder_eq_mul]
  calc (3 : ℝ) ^ (rhoDr * (l : ℝ)) * bridgeCmpRemainder C Cd g rhoDr E jStar mq mq' v
      ≤ (3 : ℝ) ^ (rhoDr * (l : ℝ)) *
          (C * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
                (1 + 2 / (rhoDr * Real.log 3)) *
                Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
              (2 + Pi) * (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
            Real.exp (-(k : ℝ) * (rhoDr * (l0 : ℝ) * Real.log 3 / 2 - 2 * chop))) :=
        mul_le_mul_of_nonneg_left
          (bridgeCmpRemainder_amortized (l0 := l0) hC hCd hg hrho hchop hmq hmq' hPi hkap
            hK hK' hpre hpre' hjv hscale) (by positivity)
    _ = (3 : ℝ) ^ (rhoDr * (l : ℝ)) * C *
              (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
              (1 + 2 / (rhoDr * Real.log 3)) *
              Real.exp (2 * chop - rhoDr * (l0 : ℝ) * Real.log 3 / 2) *
            (2 + Pi) * (3 : ℝ) ^ (-rhoDr * ((r0 : ℝ) - (jStar : ℝ)) / 2) *
          Real.exp (-(k : ℝ) * (rhoDr * (l0 : ℝ) * Real.log 3 / 2 - 2 * chop)) := by ring

end

end ShortHop
end HighContrast
end Homogenization
