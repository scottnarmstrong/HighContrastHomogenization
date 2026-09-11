/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.PropagationAssembly

/-!
# The propagation constant

The constant of the induction bounding the new fluctuation terms is exhibited
here, and the propagation estimate is read off it.  Admissibility of the
service length,

`λ_port = max{3^{-ha} + 2^{Q-1}C_{\rm rec}^Q3^{-hQd/2}, 3^{-ha}} ≤ 1/4`,

forces `β_h = 2^{Q-1}C_{\rm rec}^Q3^{-hQd/2} ≤ 1/4`, so the step of the induction
contracts, and

`K = 3^{ah} + 2C(d,Q,h)(1 + C(Q,a,h))`

is admissible: the start needs `3^{ah} ≤ K`, and the step needs
`β_hK + C(d,Q,h)(1 + C(Q,a,h)) ≤ K`, which holds because the second summand of
`K` is twice the constant the step adds.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **Enlarging the constant of a propagation-shaped estimate.**  The propagation
and startup displays of `p.fixed.geometry.one.grid.propagation` share one constant `C_L`, and
each of them is proved with its own; either may be raised to their maximum. -/
theorem le_of_le_const {C C' E : ℝ} (hCC : C ≤ C') (hE : 0 ≤ E - 1) {X Y : ℝ≥0∞}
    (h : Y ≤ ENNReal.ofReal C * X + ENNReal.ofReal (C * (E - 1))) :
    Y ≤ ENNReal.ofReal C' * X + ENNReal.ofReal (C' * (E - 1)) :=
  le_trans h
    (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hCC) le_rfl)
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC hE)))

section Window

variable {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- **`e.fixed.geometry.profile.fixed.span` with the constant exhibited.**  Under
the admissibility hypothesis `λ_port ≤ 1/4` of `p.fixed.geometry.one.grid.propagation`, a
unit-size profile propagates over `L` scales with the displayed constant. -/
theorem portableProfile_propagation_of_lambdaPort [NeZero d] [IsProbabilityMeasure P]
    {Q a rhoMax Crec : ℝ} (hQ : 1 ≤ Q) (ha : 0 < a) (hCrec : 0 ≤ Crec)
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
    {b h L T : ℤ} (hh : 1 ≤ h) (hL : 1 ≤ L) (hb : jStar ≤ b) (hbT : b + h ≤ T)
    (hTL : T + L ≤ TMax) (hlam : lambdaPort d Q a Crec h ≤ 1 / 4)
    (hprof : portableProfile P Q a rhoMax q jStar b T ≤ 1) :
    portableProfile P Q a rhoMax q jStar b (T + L) ≤
      ENNReal.ofReal
          (1 + (L : ℝ) *
              ((3 : ℝ) ^ (a * (h : ℝ)) +
                2 * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                  (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ))))) +
            1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
          portableProfile P Q a rhoMax q jStar b T +
        ENNReal.ofReal
          ((1 + (L : ℝ) *
                ((3 : ℝ) ^ (a * (h : ℝ)) +
                  2 * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                    (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                      (3 : ℝ) ^ (a * (h : ℝ))))) +
              1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
            (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hG0 : (0 : ℝ) ≤ (3 : ℝ) ^ (a * (h : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hm0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
      (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
        (3 : ℝ) ^ (a * (h : ℝ))) := by positivity
  have hKbase : (3 : ℝ) ^ (a * (h : ℝ)) ≤
      (3 : ℝ) ^ (a * (h : ℝ)) +
        2 * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
          (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
            (3 : ℝ) ^ (a * (h : ℝ)))) := by linarith only [hm0]
  have hK0 : (0 : ℝ) ≤ (3 : ℝ) ^ (a * (h : ℝ)) +
      2 * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
        (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
          (3 : ℝ) ^ (a * (h : ℝ)))) := le_trans hG0 hKbase
  have hbeta_le : 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q ≤ 1 / 4 := by
    have h1 := lambdaCen_le_lambdaPort d Q a Crec h
    have h2 := lambdaCen_eq d Q a Crec h
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(h : ℝ) * a) := Real.rpow_nonneg (by norm_num) _
    linarith only [h1, h2, h3, hlam]
  have hprodK := mul_le_mul_of_nonneg_right hbeta_le hK0
  refine portableProfile_propagation hQ ha hCrec hP hunit hq hlj hfin hmom hrec hh hL hb hbT
    hTL hKbase ?_ hprof
  linarith only [hprodK, hG0, hm0]

end Window

end

end PortableHistory
end HighContrast
end Homogenization
