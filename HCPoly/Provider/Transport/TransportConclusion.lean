/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.TransportAssembly
import HCPoly.Provider.Transport.TransportCoefficients

/-!
# The conclusion of the grid transport, and its source coefficient

Two things the last display of `p.two.grid.transport` needs
beyond the summed history bound.

*The conclusion in its printed shape.*  The centered half and the nonlinear half
reach their target with independent constants on the transported source rows —
the centered half pays the convolution of the source rows against the profile
weights at the centered target weight, the nonlinear half at the nonlinear one
— so the closing step admits two source constants, not one.  The conclusion
below is the printed `e.two.grid.profile` exactly: one constant above the
two profile coefficients and above the two source coefficients, the buffer
factor `3^{2aℓ₀}` on the profile and the single factor `3^{aℓ₀}` on the
majorant.

*The source coefficient.*  The residual that the filling of a target cell leaves
is measured by `e.two.grid.whitney.fine.bound` against
`𝖣_cont^{tr,𝒮} = C_dK(q,q')κ_𝐄B_qB_{q'}χ_g𝒰²`, while the proof of the row
produces the geometric series `ζ_g` and the grid constant `6d^{3/2}K_hop` in its
place.  The two are the same up to a factor that depends on `d` and `K_hop`
alone: `ζ_g = 3^{1-g}χ_g ≤ 3χ_g`, the multiplier mean is at most `𝒰 = 2`, and
`C_d ≥ 1` and `K(q,q') ≥ 1` only help.  Raising a factor `Λ ≥ 1` on the total
source coefficient to the majorant costs `Λ^Q`, which the transport's base
constant carries because it is fixed before the dimensional constant, the law,
the reference block and the two witnesses.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The printed conclusion -/

/-- **`e.two.grid.profile`.**  The two halves of the
transported history add to the printed conclusion, with independent source
constants: any `C_tr` above both the sum of the two profile coefficients and the
sum of the two source coefficients is admissible. -/
theorem transport_conclusion_of_histories {P : Measure (CoeffSpace d)}
    {Q a rhoMax : ℝ} {q q' : Mat d} {Ccen Cnl CcenS CnlS Ctr etaX Rsrc l0 : ℝ}
    {jStar b t n : ℤ} (heta : 0 ≤ etaX) (hR : 0 ≤ Rsrc) (hCcen : 0 ≤ Ccen)
    (hCnl : 0 ≤ Cnl) (hCcenS : 0 ≤ CcenS) (hCnlS : 0 ≤ CnlS)
    (hCtr : Ccen + Cnl ≤ Ctr) (hCtrS : CcenS + CnlS ≤ Ctr)
    (hcen : centeredHistory P Q rhoMax q' jStar n ≤
      ENNReal.ofReal (Ccen * (3 : ℝ) ^ (2 * a * l0)) *
          portableProfile P Q a rhoMax q jStar b t +
        ENNReal.ofReal (Ccen * etaX) +
        ENNReal.ofReal (CcenS * (3 : ℝ) ^ (a * l0) * Rsrc))
    (hnl : nonlinearHistory P Q a q' jStar n ≤
      ENNReal.ofReal (Cnl * (3 : ℝ) ^ (2 * a * l0)) *
          portableProfile P Q a rhoMax q jStar b t +
        ENNReal.ofReal (Cnl * etaX) +
        ENNReal.ofReal (CnlS * (3 : ℝ) ^ (a * l0) * Rsrc)) :
    centeredHistory P Q rhoMax q' jStar n + nonlinearHistory P Q a q' jStar n ≤
      ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * l0)) *
          portableProfile P Q a rhoMax q jStar b t +
        ENNReal.ofReal (Ctr * etaX) +
        ENNReal.ofReal (Ctr * (3 : ℝ) ^ (a * l0) * Rsrc) := by
  have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * a * l0) := Real.rpow_nonneg (by norm_num) _
  have hs0 : (0 : ℝ) ≤ (3 : ℝ) ^ (a * l0) * Rsrc :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hR
  refine (add_le_add hcen hnl).trans ?_
  have hprof : ENNReal.ofReal (Ccen * (3 : ℝ) ^ (2 * a * l0)) *
        portableProfile P Q a rhoMax q jStar b t +
      ENNReal.ofReal (Cnl * (3 : ℝ) ^ (2 * a * l0)) *
        portableProfile P Q a rhoMax q jStar b t ≤
      ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * l0)) *
        portableProfile P Q a rhoMax q jStar b t := by
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCcen hb0) (mul_nonneg hCnl hb0),
      ← add_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCtr hb0)) le_rfl
  have hbr : ENNReal.ofReal (Ccen * etaX) + ENNReal.ofReal (Cnl * etaX) ≤
      ENNReal.ofReal (Ctr * etaX) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hCcen heta) (mul_nonneg hCnl heta), ← add_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCtr heta)
  have hsrc : ENNReal.ofReal (CcenS * (3 : ℝ) ^ (a * l0) * Rsrc) +
      ENNReal.ofReal (CnlS * (3 : ℝ) ^ (a * l0) * Rsrc) ≤
      ENNReal.ofReal (Ctr * (3 : ℝ) ^ (a * l0) * Rsrc) := by
    rw [show CcenS * (3 : ℝ) ^ (a * l0) * Rsrc =
        CcenS * ((3 : ℝ) ^ (a * l0) * Rsrc) from by ring,
      show CnlS * (3 : ℝ) ^ (a * l0) * Rsrc =
        CnlS * ((3 : ℝ) ^ (a * l0) * Rsrc) from by ring,
      show Ctr * (3 : ℝ) ^ (a * l0) * Rsrc =
        Ctr * ((3 : ℝ) ^ (a * l0) * Rsrc) from by ring,
      ← ENNReal.ofReal_add (mul_nonneg hCcenS hs0) (mul_nonneg hCnlS hs0), ← add_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCtrS hs0)
  have hregroup : ∀ x1 y1 z1 x2 y2 z2 : ℝ≥0∞,
      x1 + y1 + z1 + (x2 + y2 + z2) = x1 + x2 + (y1 + y2) + (z1 + z2) := by
    intro x1 y1 z1 x2 y2 z2
    ring
  rw [hregroup]
  exact add_le_add (add_le_add hprof hbr) hsrc

/-! ## The source coefficient of the rows -/

/-- `ζ_g = 3^{1-g}χ_g ≤ 3χ_g`: the two geometric series of the subsection differ
by the single scale factor, which is at most three below the critical
exponent. -/
theorem zetaG_le_three_mul_chiG {g : ℝ} (hg0 : 0 ≤ g) (hg : g < 1) :
    zetaG g ≤ 3 * chiG g := by
  have hx1 : (1 : ℝ) < (3 : ℝ) ^ (1 - g) :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr
      (Or.inl ⟨by norm_num, by linarith only [hg]⟩)
  have hx3 : (3 : ℝ) ^ (1 - g) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith only [hg0] : 1 - g ≤ (1 : ℝ))
    rwa [Real.rpow_one] at h
  have hden : (0 : ℝ) < (3 : ℝ) ^ (1 - g) - 1 := by linarith only [hx1]
  have hxpos : (0 : ℝ) < (3 : ℝ) ^ (1 - g) := by linarith only [hx1]
  rw [zetaG, chiG, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    show (1 - ((3 : ℝ) ^ (1 - g))⁻¹)⁻¹ =
      (3 : ℝ) ^ (1 - g) / ((3 : ℝ) ^ (1 - g) - 1) from by field_simp,
    ← div_eq_mul_inv]
  gcongr

/-- **The source row coefficient is the printed one, up to a grid factor.**  The
coefficient that the filling of a target cell produces —
`6d^{3/2}K_hop B_q ζ_g 𝒰` against the reference ratio and the second boundary
constant — is at most `18d^{3/2}K_hop` times the printed continued coefficient
`𝖣_cont^{tr,𝒮}`, uniformly in the dimensional constant and in the two witnesses.

Three facts and nothing else: `ζ_g ≤ 3χ_g`, the multiplier mean is at most
`𝒰 = 2`, and both `C_d` and the cross-grid factor are at least one. -/
theorem srcRow_coefficient_absorbed (hd : 1 ≤ d) {g Cd Khop U : ℝ} (hg0 : 0 ≤ g)
    (hg : g < 1) (hCd : 1 ≤ Cd) (E : BlockMat d) {jStar : ℤ} (mu mu' : Mat d)
    (hK : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop)
    (hU0 : 0 ≤ U) (hU : U ≤ 2) :
    6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu * zetaG g * U *
        (kappaRef E * (boundaryConst Cd g mu' * U)) ≤
      18 * (d : ℝ) * Real.sqrt d * Khop *
        transportContCoeff Cd g E jStar mu mu' := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hK1 : (1 : ℝ) ≤ gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') :=
    one_le_gridRatio _ _
  have hKhop : (1 : ℝ) ≤ Khop := le_trans hK1 hK
  have hkap : (0 : ℝ) ≤ kappaRef E := by
    rw [kappaRef, blockSize]
    exact Real.sInf_nonneg fun _ hx => hx.1
  have hB : (0 : ℝ) ≤ boundaryConst Cd g mu :=
    zero_le_boundaryConst (le_trans zero_le_one hCd) hg mu
  have hB' : (0 : ℝ) ≤ boundaryConst Cd g mu' :=
    zero_le_boundaryConst (le_trans zero_le_one hCd) hg mu'
  have hchi : (0 : ℝ) < chiG g := by
    have h : (1 : ℝ) < (3 : ℝ) ^ (1 - g) :=
      (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr
        (Or.inl ⟨by norm_num, by linarith only [hg]⟩)
    exact inv_pos.mpr (by linarith only [h])
  have hzeta0 : (0 : ℝ) ≤ zetaG g := by
    have hlt : (3 : ℝ) ^ (-(1 - g)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg])
    rw [zetaG]
    exact (inv_pos.mpr (by linarith only [hlt])).le
  have hUU : U * U ≤ 4 := by
    have h := mul_le_mul hU hU hU0 (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [h]
  have hCK : (1 : ℝ) ≤
      Cd * gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') := by
    have h := mul_le_mul hCd hK1 zero_le_one (le_trans zero_le_one hCd)
    linarith only [h]
  have hzeta := zetaG_le_three_mul_chiG hg0 hg
  have hcore : zetaG g * (U * U) ≤
      12 * (Cd * gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) *
        chiG g := by
    have ha : zetaG g * (U * U) ≤ zetaG g * 4 := mul_le_mul_of_nonneg_left hUU hzeta0
    have hb : zetaG g * 4 ≤ 3 * chiG g * 4 :=
      mul_le_mul_of_nonneg_right hzeta (by norm_num)
    have hc := mul_le_mul_of_nonneg_right hCK (by positivity : (0 : ℝ) ≤ 12 * chiG g)
    linarith only [ha, hb, hc]
  rw [transportContCoeff]
  calc 6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu * zetaG g * U *
        (kappaRef E * (boundaryConst Cd g mu' * U))
      = 6 * (d : ℝ) * Real.sqrt d * Khop * (zetaG g * (U * U)) *
          (kappaRef E * (boundaryConst Cd g mu * boundaryConst Cd g mu')) := by ring
    _ ≤ 6 * (d : ℝ) * Real.sqrt d * Khop *
          (12 * (Cd * gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) *
            chiG g) *
          (kappaRef E * (boundaryConst Cd g mu * boundaryConst Cd g mu')) := by gcongr
    _ = 18 * (d : ℝ) * Real.sqrt d * Khop *
          (Cd * gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') *
            kappaRef E * boundaryConst Cd g mu * boundaryConst Cd g mu' * chiG g *
            4) := by ring

/-- **A grid factor on the source coefficient costs its `Q`-th power on the
majorant.**  If the total source coefficient a proof produces is at most `Λ`
times the printed one, then the source total it produces is at most `Λ^Q` times
the printed majorant `𝓡_src^{tr,𝒮}`.

The transport's base constant carries `Λ^Q` because `Λ` depends only on the
dimension and the hop constant, and the base constant is fixed before the
dimensional constant, the law, the reference block and the two witnesses. -/
theorem srcRemainder_absorbed {Dsrc Lam Cd g Q a : ℝ} (hQ : 1 ≤ Q) (hL : 1 ≤ Lam)
    (h0 : 0 ≤ Dsrc) (E : BlockMat d) {jStar : ℤ} (mu mu' : Mat d) (n : ℤ)
    (hCd : 0 ≤ Cd) (hg : g < 1)
    (hD : Dsrc ≤ Lam * transportSrcCoeff Cd g E jStar mu mu') :
    (Dsrc + Dsrc ^ Q) * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) ≤
      Lam ^ Q * transportSrcRemainder Cd g Q a E jStar mu mu' n := by
  have hD1 : (1 : ℝ) ≤ transportSrcCoeff Cd g E jStar mu mu' :=
    one_le_transportSrcCoeff hCd hg E jStar mu mu'
  have hD0 : (0 : ℝ) ≤ transportSrcCoeff Cd g E jStar mu mu' := le_trans zero_le_one hD1
  have hL0 : (0 : ℝ) ≤ Lam := le_trans zero_le_one hL
  have hLQ : Lam ≤ Lam ^ Q := by
    have h := Real.rpow_le_rpow_of_exponent_le hL hQ
    rwa [Real.rpow_one] at h
  have h1 : Dsrc ≤ Lam ^ Q * transportSrcCoeff Cd g E jStar mu mu' :=
    le_trans hD (mul_le_mul_of_nonneg_right hLQ hD0)
  have h2 : Dsrc ^ Q ≤ Lam ^ Q * transportSrcCoeff Cd g E jStar mu mu' ^ Q := by
    refine le_trans (Real.rpow_le_rpow h0 hD (le_trans zero_le_one hQ)) ?_
    exact le_of_eq (Real.mul_rpow hL0 hD0)
  have hexp : Lam ^ Q * (transportSrcCoeff Cd g E jStar mu mu' +
      transportSrcCoeff Cd g E jStar mu mu' ^ Q) =
      Lam ^ Q * transportSrcCoeff Cd g E jStar mu mu' +
        Lam ^ Q * transportSrcCoeff Cd g E jStar mu mu' ^ Q := by ring
  rw [transportSrcRemainder, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith only [h1, h2, hexp])
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)

end

end Transport
end HighContrast
end Homogenization
