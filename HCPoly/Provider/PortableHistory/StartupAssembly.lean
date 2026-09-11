/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Startup

/-!
# The startup estimate

`e.fixed.geometry.profile.startup` is the propagation of a unit-size complete
history over a bounded number of scales:

`𝒫_q(b+L;b) ≤ C_L𝓗_q(b) + C_L(e^{QΔ_{b,b+L}^q} - 1)`   when `𝓗_q(b) ≤ 1`.

The three rows of `e.scale.selection.complete.profile` are added.  The inherited row
contributes `e^{QD}𝓗_q(b)`, the `L` new centered scales contribute
`2dL2^{Q-1}C_{\rm rec}^Qe^{QD}𝓗_q(b)` through the checkpoint display
`(v_b^q)^Q ≤ 2d𝓗_q^{cen}(b)`, and the `L` new nonlinear terms contribute
`L(e^{QD} - 1)`.  Every factor `e^{QD}` meets a quantity below one, and the
unit-size absorption `e^{QD}X ≤ X + (e^{QD} - 1)` converts each of them into an
additive error proportional to `e^{QD} - 1`.

The constant is exhibited:
`C_L = 1 + L + 2dL2^{Q-1}C_{\rm rec}^Q + L2^{Q-1}C_{\rm rec}^Q2^Q`.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

section Window

variable {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- **`e.fixed.geometry.profile.startup`.**  A unit-size complete history at the
checkpoint propagates over `L` scales at the cost of a constant depending only
on `d, Q, a, ρ_max, h, L`, with no scale-independent positive error. -/
theorem portableProfile_startup [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax Crec : ℝ}
    (hQ : 1 ≤ Q) (ha : 0 < a) (hCrec : 0 ≤ Crec)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    (hmom : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → centeredMoment P Q q j ≠ ⊤)
    (hrec :
      ∀ (P : Measure (CoeffSpace d)),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        ∀ (l : ℤ) (q : Mat d),
          IsRoundedGrid l q →
          ∀ j h : ℤ, l ≤ j → 1 ≤ h →
            Book.Ch02.BlockPosDef (adaptedMean P q j) →
            Book.Ch02.BlockPosDef (adaptedMean P q (j + h)) →
            HasFiniteAdaptedMean P q j →
            HasFiniteAdaptedMean P q (j + h) →
            centeredMoment P Q q j ≠ ⊤ →
            centeredMoment P Q q (j + h) ≠ ⊤ →
            0 ≤ detIncrement P q j (j + h) ∧
              centeredMoment P Q q (j + h) ≤
                ENNReal.ofReal
                    (Crec * (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) *
                      Real.exp (detIncrement P q j (j + h))) *
                  centeredMoment P Q q j +
                ENNReal.ofReal (Crec * gainPhi Q (detIncrement P q j (j + h))))
    {b L : ℤ} (hL : 1 ≤ L) (hb : jStar ≤ b) (hbL : b + L ≤ TMax)
    (hhist : portableHistory P Q a rhoMax q jStar b ≤ 1) :
    portableProfile P Q a rhoMax q jStar b (b + L) ≤
      ENNReal.ofReal (1 + (L : ℝ) + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) +
            (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q)) *
          portableHistory P Q a rhoMax q jStar b +
        ENNReal.ofReal
          ((1 + (L : ℝ) + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) +
              (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q)) *
            (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans zero_le_one hL
  have hK0 : (0 : ℝ) ≤ (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) := by positivity
  have hc0 : (0 : ℝ) ≤ (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) := by positivity
  have hD0 : 0 ≤ detIncrement P q b (b + L) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj hb) (by omega) (hfin b hb (by omega))
      (hfin (b + L) (by omega) hbL)
  have hE1 : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q b (b + L)) :=
    Real.one_le_exp (mul_nonneg hQ0 hD0)
  have hE0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q b (b + L)) - 1 := by
    linarith only [hE1]
  -- the checkpoint moment against the complete history
  have hcen : centeredHistory P Q rhoMax q jStar b ≤ portableHistory P Q a rhoMax q jStar b := by
    rw [portableHistory]
    exact le_self_add
  have hvb : centeredMoment P Q q b ^ Q ≤
      ENNReal.ofReal (2 * (d : ℝ)) * portableHistory P Q a rhoMax q jStar b :=
    le_trans
      (centeredMoment_rpow_le_centeredHistory (Recurrence.posDef_of_isRoundedGrid hq)
        (lt_of_lt_of_le zero_lt_one hQ) hb
        (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq b (hfin b hb (by omega))))
      (mul_le_mul' le_rfl hcen)
  -- the inherited row
  have hI : ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b (b + L)))) *
        portableHistory P Q a rhoMax q jStar b ≤
      portableHistory P Q a rhoMax q jStar b +
        ENNReal.ofReal (Real.exp (Q * detIncrement P q b (b + L)) - 1) :=
    le_trans (startup_inherited hQ0 ha hP hq hlj hfin hL hb hbL)
      (ofReal_mul_le_add_of_le_one hE1 hhist)
  -- the new centered scales
  have hV : ∑ j ∈ Finset.Icc (b + 1) (b + L),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (b + L))) *
          centeredMoment P Q q j ^ Q ≤
      (ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) *
            portableHistory P Q a rhoMax q jStar b +
          ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) *
            (Real.exp (Q * detIncrement P q b (b + L)) - 1))) +
        ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
          (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
    refine le_trans (startup_centered hQ ha hCrec hP hunit hq hlj hfin hmom hrec hL hb hbL)
      (add_le_add ?_ le_rfl)
    calc ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q) *
            Real.exp (Q * detIncrement P q b (b + L))) *
          centeredMoment P Q q b ^ Q
        ≤ ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q) *
              Real.exp (Q * detIncrement P q b (b + L))) *
            (ENNReal.ofReal (2 * (d : ℝ)) * portableHistory P Q a rhoMax q jStar b) :=
          mul_le_mul' le_rfl hvb
      _ = ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q) *
              Real.exp (Q * detIncrement P q b (b + L)) * (2 * (d : ℝ))) *
            portableHistory P Q a rhoMax q jStar b :=
          ofReal_mul_ofReal_mul (by positivity) _ _
      _ = ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) *
              Real.exp (Q * detIncrement P q b (b + L))) *
            portableHistory P Q a rhoMax q jStar b := by
          rw [show (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q) *
                Real.exp (Q * detIncrement P q b (b + L)) * (2 * (d : ℝ)) =
              (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) *
                Real.exp (Q * detIncrement P q b (b + L)) from by ring]
      _ = ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) *
            (ENNReal.ofReal (Real.exp (Q * detIncrement P q b (b + L))) *
              portableHistory P Q a rhoMax q jStar b) :=
          (ofReal_mul_ofReal_mul hK0 _ _).symm
      _ ≤ ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) *
            (portableHistory P Q a rhoMax q jStar b +
              ENNReal.ofReal (Real.exp (Q * detIncrement P q b (b + L)) - 1)) :=
          mul_le_mul' le_rfl (ofReal_mul_le_add_of_le_one hE1 hhist)
      _ = ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) *
            portableHistory P Q a rhoMax q jStar b +
          ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) *
            (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
          rw [mul_add, ← ENNReal.ofReal_mul hK0]
  -- the new nonlinear terms
  have hN := startup_nonlinear (a := a) hQ0 ha hP hq hlj hfin hL hb hbL
  -- the assembly
  have e2 : (0 : ℝ) ≤ (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) *
      (Real.exp (Q * detIncrement P q b (b + L)) - 1) := mul_nonneg hK0 hE0
  have e3 : (0 : ℝ) ≤ (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
      (Real.exp (Q * detIncrement P q b (b + L)) - 1) := mul_nonneg hc0 hE0
  have e4 : (0 : ℝ) ≤ (L : ℝ) * (Real.exp (Q * detIncrement P q b (b + L)) - 1) :=
    mul_nonneg hL0 hE0
  have herr : ENNReal.ofReal (Real.exp (Q * detIncrement P q b (b + L)) - 1) +
        ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) *
          (Real.exp (Q * detIncrement P q b (b + L)) - 1)) +
        ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
          (Real.exp (Q * detIncrement P q b (b + L)) - 1)) +
        ENNReal.ofReal ((L : ℝ) * (Real.exp (Q * detIncrement P q b (b + L)) - 1)) =
      ENNReal.ofReal
        ((1 + (L : ℝ) + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) +
            (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q)) *
          (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
    rw [← ENNReal.ofReal_add hE0 e2, ← ENNReal.ofReal_add (by linarith only [hE0, e2]) e3,
      ← ENNReal.ofReal_add (by linarith only [hE0, e2, e3]) e4]
    congr 1
    ring
  have hhistbound : portableHistory P Q a rhoMax q jStar b +
        ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) *
          portableHistory P Q a rhoMax q jStar b ≤
      ENNReal.ofReal (1 + (L : ℝ) + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) +
          (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q)) *
        portableHistory P Q a rhoMax q jStar b := by
    have hone : (1 : ℝ≥0∞) +
        ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) =
        ENNReal.ofReal (1 + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hK0]
    calc portableHistory P Q a rhoMax q jStar b +
          ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) *
            portableHistory P Q a rhoMax q jStar b
        = (1 + ENNReal.ofReal ((L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q))) *
            portableHistory P Q a rhoMax q jStar b := by
          rw [add_mul, one_mul]
      _ = ENNReal.ofReal (1 + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q)) *
            portableHistory P Q a rhoMax q jStar b := by rw [hone]
      _ ≤ ENNReal.ofReal (1 + (L : ℝ) + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ (Q - 1) * Crec ^ Q) +
              (L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q)) *
            portableHistory P Q a rhoMax q jStar b :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith only [hL0, hc0])) le_rfl
  simp only [portableProfile]
  have hcomb := add_le_add (add_le_add hI hV) hN
  have htarget := add_le_add hhistbound (le_of_eq herr)
  refine le_trans hcomb (le_trans (le_of_eq ?_) htarget)
  ring

end Window

end

end PortableHistory
end HighContrast
end Homogenization
