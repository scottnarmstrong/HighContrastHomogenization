/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.Eccentricity
import HCPoly.Provider.Transport.CoefficientArithmetic
import HCPoly.Provider.Transport.TransportCoefficients

/-!
# Finite-prefix transport source amortization

This file proves the coefficient estimate and scale cancellation behind the
geometric smallness of the transported source remainder along the sequence of
geometry changes (`p.two.grid.transport`).  The prefix projective bounds control
both boundary constants, the scale rule pays one buffer length,
and the remaining hop dependence is a decreasing exponential once the buffer
threshold is strict.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

variable {d : ℕ}

/-- The transport source coefficient at two witnesses in a projective prefix
has the printed `(2 + Π)e^{2t}` bound. -/
theorem transportSrcCoeff_le [NeZero d] {Cd g Khop Pi t : ℝ}
    {E : BlockMat d} {jStar : ℤ} {mu mu' : Mat d}
    (hCd : 0 ≤ Cd) (hg : g < 1) (ht : 0 ≤ t)
    (hmu : mu.PosDef) (hmu' : mu'.PosDef) (hPi : 1 ≤ Pi)
    (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop)
    (hpre : projDist 1 mu ≤ t) (hpre' : projDist 1 mu' ≤ t) :
    transportSrcCoeff Cd g E jStar mu mu' ≤
      (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
        (2 + Pi) * Real.exp (2 * t) := by
  have hKhop : (0 : ℝ) ≤ Khop :=
    le_trans (le_trans zero_le_one (Transport.one_le_gridRatio _ _)) hK
  have hchi : 0 < chiG g := Transport.zero_lt_chiG hg
  have hzeta : 0 < zetaG g := Transport.zero_lt_zetaG hg
  have hkap0 : (0 : ℝ) ≤ kappaRef E := Transport.zero_le_kappaRef E
  have hPi0 : (0 : ℝ) ≤ 6 * Pi := by linarith only [hPi]
  set beta : ℝ := Cd * Real.exp t * zetaG g with hbeta
  have hbeta0 : 0 ≤ beta := by
    rw [hbeta]
    exact mul_nonneg (mul_nonneg hCd (Real.exp_pos _).le) hzeta.le
  have hB : boundaryConst Cd g mu ≤ beta := by
    rw [hbeta]
    exact ShortHop.boundaryConst_le_exp hCd hg hmu hpre
  have hB' : boundaryConst Cd g mu' ≤ beta := by
    rw [hbeta]
    exact ShortHop.boundaryConst_le_exp hCd hg hmu' hpre'
  have hB0 : 0 ≤ boundaryConst Cd g mu := Transport.zero_le_boundaryConst hCd hg mu
  have hB0' : 0 ≤ boundaryConst Cd g mu' := Transport.zero_le_boundaryConst hCd hg mu'
  have hBB : boundaryConst Cd g mu * boundaryConst Cd g mu' ≤ beta * beta :=
    mul_le_mul hB hB' hB0' hbeta0
  have hkBB : kappaRef E * (boundaryConst Cd g mu * boundaryConst Cd g mu') ≤
      6 * Pi * (beta * beta) :=
    mul_le_mul hkap hBB (mul_nonneg hB0 hB0') hPi0
  have hinner : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') *
      (kappaRef E * (boundaryConst Cd g mu * boundaryConst Cd g mu')) ≤
        Khop * (6 * Pi * (beta * beta)) :=
    mul_le_mul hK hkBB (mul_nonneg hkap0 (mul_nonneg hB0 hB0')) hKhop
  have hcont : transportContCoeff Cd g E jStar mu mu' ≤
      Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 := by
    have hfront : (0 : ℝ) ≤ Cd * chiG g * 4 :=
      mul_nonneg (mul_nonneg hCd hchi.le) (by norm_num)
    calc
      transportContCoeff Cd g E jStar mu mu' =
          Cd * chiG g * 4 *
            (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') *
              (kappaRef E * (boundaryConst Cd g mu * boundaryConst Cd g mu'))) := by
        rw [transportContCoeff]
        ring
      _ ≤ Cd * chiG g * 4 * (Khop * (6 * Pi * (beta * beta))) :=
        mul_le_mul_of_nonneg_left hinner hfront
      _ = Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 := by ring
  have hsq : boundaryConst Cd g mu' ^ 2 ≤ beta ^ 2 :=
    pow_le_pow_left₀ hB0' hB' 2
  have hkSq : kappaRef E * boundaryConst Cd g mu' ^ 2 ≤
      6 * Pi * beta ^ 2 := mul_le_mul hkap hsq (sq_nonneg _) hPi0
  have hearly : transportEarlyCoeff Cd g E mu' ≤
      Cd * (6 * Pi) * beta ^ 2 * 4 := by
    have hfront : (0 : ℝ) ≤ Cd * 4 := mul_nonneg hCd (by norm_num)
    calc
      transportEarlyCoeff Cd g E mu' =
          Cd * 4 * (kappaRef E * boundaryConst Cd g mu' ^ 2) := by
        rw [transportEarlyCoeff]
        ring
      _ ≤ Cd * 4 * (6 * Pi * beta ^ 2) := mul_le_mul_of_nonneg_left hkSq hfront
      _ = Cd * (6 * Pi) * beta ^ 2 * 4 := by ring
  have hsrc : transportSrcCoeff Cd g E jStar mu mu' ≤
      1 + (Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 +
        Cd * (6 * Pi) * beta ^ 2 * 4) := by
    rw [transportSrcCoeff]
    linarith only [hcont, hearly]
  have hexp : Real.exp t * Real.exp t = Real.exp (2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsum : Cd * Khop * (6 * Pi) * beta * beta * chiG g * 4 +
        Cd * (6 * Pi) * beta ^ 2 * 4 =
      24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) * Pi *
        Real.exp (2 * t) := by
    rw [← hexp, hbeta]
    ring
  have hM0 : (0 : ℝ) ≤
      24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have hlast : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have := mul_nonneg hKhop hchi.le
      linarith only [this]
    exact mul_nonneg (mul_nonneg (by linarith only [hCd]) (sq_nonneg _)) hlast
  have hX : (1 : ℝ) ≤ Real.exp (2 * t) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [ht])
  have hfinal := Transport.one_add_mul_le hM0 hPi hX
  linarith only [hsrc, hsum, hfinal]

/-- The coefficient and its `Q`-power have the prefix bound appearing in the
transport source majorant. -/
theorem transportSrcCoeff_add_rpow_le [NeZero d] {Cd g Khop Pi t Q : ℝ}
    {E : BlockMat d} {jStar : ℤ} {mu mu' : Mat d}
    (hCd : 0 ≤ Cd) (hg : g < 1) (ht : 0 ≤ t) (hQ : 1 ≤ Q)
    (hmu : mu.PosDef) (hmu' : mu'.PosDef) (hPi : 1 ≤ Pi)
    (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop)
    (hpre : projDist 1 mu ≤ t) (hpre' : projDist 1 mu' ≤ t) :
    transportSrcCoeff Cd g E jStar mu mu' +
        transportSrcCoeff Cd g E jStar mu mu' ^ Q ≤
      2 * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
        (2 + Pi) ^ Q * Real.exp (2 * Q * t) := by
  let D := transportSrcCoeff Cd g E jStar mu mu'
  let M := 1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)
  let X := M * (2 + Pi) * Real.exp (2 * t)
  have hD1 : 1 ≤ D := Transport.one_le_transportSrcCoeff hCd hg E jStar mu mu'
  have hDX : D ≤ X := transportSrcCoeff_le hCd hg ht hmu hmu' hPi hkap hK hpre hpre'
  have hKhop : (0 : ℝ) ≤ Khop :=
    le_trans (le_trans zero_le_one (Transport.one_le_gridRatio _ _)) hK
  have hM : 1 ≤ M := by
    dsimp [M]
    have hchi := (Transport.zero_lt_chiG hg).le
    have hlast : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have := mul_nonneg hKhop hchi
      linarith only [this]
    have hprod := mul_nonneg (mul_nonneg (by linarith only [hCd] : (0 : ℝ) ≤ 24 * Cd)
      (sq_nonneg (Cd * zetaG g))) hlast
    linarith only [hprod]
  have hX : 1 ≤ X := by
    dsimp [X]
    have hPi0 : 1 ≤ 2 + Pi := by linarith only [hPi]
    have he : 1 ≤ Real.exp (2 * t) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith only [ht])
    exact le_trans hM (le_trans
      (le_mul_of_one_le_right (by linarith only [hM]) hPi0)
      (le_mul_of_one_le_right (mul_nonneg (by linarith only [hM])
        (by linarith only [hPi0])) he))
  have hDQ : D ≤ D ^ Q := by
    have hstep := Real.rpow_le_rpow_of_exponent_le hD1 hQ
    simpa only [Real.rpow_one] using hstep
  have hpow : D ^ Q ≤ X ^ Q :=
    Real.rpow_le_rpow (by linarith only [hD1]) hDX (by linarith only [hQ])
  have hadd : D + D ^ Q ≤ 2 * X ^ Q := by linarith only [hDQ, hpow]
  refine hadd.trans_eq ?_
  dsimp [X, M]
  rw [Real.mul_rpow (mul_nonneg (by linarith only [hM])
      (by linarith only [hPi])) (Real.exp_pos _).le,
    Real.mul_rpow (by linarith only [hM]) (by linarith only [hPi]),
    ← Real.exp_mul]
  rw [show 2 * t * Q = 2 * Q * t by ring]
  ring

/-- The finite-prefix transport majorant after the exact cancellation of one
buffer length (`e.bridge.profile.source.bound`). -/
theorem transportSrcRemainder_amortized [NeZero d]
    {Ctr Cd g Khop Pi Q a chop : ℝ} {E : BlockMat d}
    {jStar r0 n l0 : ℤ} {k : ℕ} {mu mu' : Mat d}
    (hCtr : 0 ≤ Ctr) (hCd : 0 ≤ Cd) (hg : g < 1) (hQ : 1 ≤ Q)
    (ha : 0 < a) (hchop : 0 ≤ chop) (hmu : mu.PosDef) (hmu' : mu'.PosDef)
    (hPi : 1 ≤ Pi) (hkap : kappaRef E ≤ 6 * Pi)
    (hK : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop)
    (hpre : projDist 1 mu ≤ ((k : ℝ) + 1) * chop)
    (hpre' : projDist 1 mu' ≤ ((k : ℝ) + 1) * chop)
    (hscale : (r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ) ≤
      (n : ℝ) - (jStar : ℝ)) :
    Ctr * (3 : ℝ) ^ (a * (l0 : ℝ)) *
        transportSrcRemainder Cd g Q a E jStar mu mu' n ≤
      2 * Ctr *
          (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
        (2 + Pi) ^ Q * (3 : ℝ) ^ (-a * ((r0 : ℝ) - (jStar : ℝ))) *
        Real.exp (2 * Q * chop) *
        Real.exp (-(k : ℝ) * (a * (l0 : ℝ) * Real.log 3 - 2 * Q * chop)) := by
  have ht : (0 : ℝ) ≤ ((k : ℝ) + 1) * chop :=
    mul_nonneg (by positivity) hchop
  have hcoeff := transportSrcCoeff_add_rpow_le hCd hg ht hQ hmu hmu' hPi hkap hK
    hpre hpre'
  have hexponents : -a * ((n : ℝ) - (jStar : ℝ)) ≤
      -a * ((r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ)) := by
    exact mul_le_mul_of_nonpos_left hscale (by linarith only [ha])
  have hgeo : (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) ≤
      (3 : ℝ) ^
        (-a * ((r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponents
  have hKhop : (0 : ℝ) ≤ Khop :=
    le_trans (le_trans zero_le_one (Transport.one_le_gridRatio _ _)) hK
  have hM0 : (0 : ℝ) ≤
      1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have hlast : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have := mul_nonneg hKhop (Transport.zero_lt_chiG hg).le
      linarith only [this]
    have hprod := mul_nonneg
      (mul_nonneg (by linarith only [hCd] : (0 : ℝ) ≤ 24 * Cd)
        (sq_nonneg (Cd * zetaG g))) hlast
    linarith only [hprod]
  have hbound0 : (0 : ℝ) ≤
      2 * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
        (2 + Pi) ^ Q * Real.exp (2 * Q * (((k : ℝ) + 1) * chop)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg hM0 _)) (Real.rpow_nonneg (by linarith only [hPi]) _))
      (Real.exp_pos _).le
  have hterm := mul_le_mul hcoeff hgeo (Real.rpow_nonneg (by norm_num) _)
    hbound0
  have hpref : 0 ≤ Ctr * (3 : ℝ) ^ (a * (l0 : ℝ)) :=
    mul_nonneg hCtr (by positivity)
  calc
    Ctr * (3 : ℝ) ^ (a * (l0 : ℝ)) *
        transportSrcRemainder Cd g Q a E jStar mu mu' n =
      (Ctr * (3 : ℝ) ^ (a * (l0 : ℝ))) *
        ((transportSrcCoeff Cd g E jStar mu mu' +
            transportSrcCoeff Cd g E jStar mu mu' ^ Q) *
          (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) := by
        rw [transportSrcRemainder]
    _ ≤ (Ctr * (3 : ℝ) ^ (a * (l0 : ℝ))) *
      ((2 * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
          (2 + Pi) ^ Q * Real.exp (2 * Q * (((k : ℝ) + 1) * chop))) *
        (3 : ℝ) ^
          (-a * ((r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hterm hpref
    _ = 2 * Ctr *
          (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
        (2 + Pi) ^ Q * (3 : ℝ) ^ (-a * ((r0 : ℝ) - (jStar : ℝ))) *
        Real.exp (2 * Q * chop) *
        Real.exp (-(k : ℝ) * (a * (l0 : ℝ) * Real.log 3 - 2 * Q * chop)) := by
      simp_rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      have hcomb :
          Real.exp (Real.log 3 * (a * (l0 : ℝ))) *
              Real.exp (2 * Q * (((k : ℝ) + 1) * chop)) *
              Real.exp (Real.log 3 *
                (-a * ((r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ)))) =
            Real.exp (Real.log 3 * (-a * ((r0 : ℝ) - (jStar : ℝ)))) *
              Real.exp (2 * Q * chop) *
              Real.exp (-(k : ℝ) *
                (a * (l0 : ℝ) * Real.log 3 - 2 * Q * chop)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        Ctr * Real.exp (Real.log 3 * (a * (l0 : ℝ))) *
            (2 * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
                (2 + Pi) ^ Q * Real.exp (2 * Q * (((k : ℝ) + 1) * chop)) *
              Real.exp (Real.log 3 *
                (-a * ((r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ))))) =
          (2 * Ctr *
              (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
              (2 + Pi) ^ Q) *
            (Real.exp (Real.log 3 * (a * (l0 : ℝ))) *
              Real.exp (2 * Q * (((k : ℝ) + 1) * chop)) *
              Real.exp (Real.log 3 *
                (-a * ((r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (l0 : ℝ))))) := by
            ring
        _ = (2 * Ctr *
              (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
              (2 + Pi) ^ Q) *
            (Real.exp (Real.log 3 * (-a * ((r0 : ℝ) - (jStar : ℝ)))) *
              Real.exp (2 * Q * chop) *
              Real.exp (-(k : ℝ) *
                (a * (l0 : ℝ) * Real.log 3 - 2 * Q * chop))) := by rw [hcomb]
        _ = 2 * Ctr *
              (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
            (2 + Pi) ^ Q *
            Real.exp (Real.log 3 * (-a * ((r0 : ℝ) - (jStar : ℝ)))) *
            Real.exp (2 * Q * chop) *
            Real.exp (-(k : ℝ) *
              (a * (l0 : ℝ) * Real.log 3 - 2 * Q * chop)) := by ring

/-- The entry-scale clause and the strict buffer threshold collapse an
amortized transport bound to the power `(2 + Π)^(Q - aB)`. -/
theorem transport_amortized_le_rpow {a B C Pi Q chop l0 : ℝ}
    {r0 jStar : ℤ} {k : ℕ} {R : ℝ}
    (ha : 0 < a) (hPi : 1 ≤ Pi) (hC : 0 ≤ C)
    (hentry : B * Real.logb 3 (2 + Pi) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hstrict : 2 * Q * chop < a * l0 * Real.log 3)
    (hboot : R ≤ C * (2 + Pi) ^ Q *
      (3 : ℝ) ^ (-a * ((r0 : ℝ) - (jStar : ℝ))) *
      Real.exp (-(k : ℝ) * (a * l0 * Real.log 3 - 2 * Q * chop))) :
    R ≤ C * (2 + Pi) ^ (Q - a * B) := by
  have hPi0 : (0 : ℝ) < 2 + Pi := by linarith only [hPi]
  have hbase : (0 : ℝ) ≤ C * (2 + Pi) ^ Q :=
    mul_nonneg hC (Real.rpow_nonneg hPi0.le _)
  have hexp : Real.exp (-(k : ℝ) * (a * l0 * Real.log 3 - 2 * Q * chop)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hgap : 0 < a * l0 * Real.log 3 - 2 * Q * chop := by
      linarith only [hstrict]
    have hkneg : -(k : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg k)
    exact mul_nonpos_of_nonpos_of_nonneg hkneg hgap.le
  have hgeo : (3 : ℝ) ^ (-a * ((r0 : ℝ) - (jStar : ℝ))) ≤
      (2 + Pi) ^ (-(a * B)) := by
    have hstep : (3 : ℝ) ^ (-a * ((r0 : ℝ) - (jStar : ℝ))) ≤
        (3 : ℝ) ^ (Real.logb 3 (2 + Pi) * (-(a * B))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hmul := mul_le_mul_of_nonpos_left hentry (neg_nonpos.mpr ha.le)
      calc
        -a * ((r0 : ℝ) - (jStar : ℝ)) ≤
            -a * (B * Real.logb 3 (2 + Pi)) := hmul
        _ = Real.logb 3 (2 + Pi) * (-(a * B)) := by ring
    refine hstep.trans_eq ?_
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) hPi0]
  have hchain : C * (2 + Pi) ^ Q *
      (3 : ℝ) ^ (-a * ((r0 : ℝ) - (jStar : ℝ))) *
      Real.exp (-(k : ℝ) * (a * l0 * Real.log 3 - 2 * Q * chop)) ≤
      C * (2 + Pi) ^ Q * (2 + Pi) ^ (-(a * B)) := by
    have h3 : (0 : ℝ) ≤
        (3 : ℝ) ^ (-a * ((r0 : ℝ) - (jStar : ℝ))) := by positivity
    have hstep₁ := mul_le_mul_of_nonneg_left hexp (mul_nonneg hbase h3)
    have hstep₂ := mul_le_mul_of_nonneg_left hgeo hbase
    rw [mul_one] at hstep₁
    exact hstep₁.trans hstep₂
  refine (hboot.trans hchain).trans_eq ?_
  rw [show Q - a * B = Q + -(a * B) by ring, Real.rpow_add hPi0]
  ring

end

end Selection
end HighContrast
end Homogenization
