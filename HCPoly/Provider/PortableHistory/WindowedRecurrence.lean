/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.GainPower
import HCPoly.Provider.Recurrence.AdaptedCellPositivity

/-!
# The recurrence read on the bounded window

`p.fixed.geometry.one.grid.propagation` carries the conclusion of `p.fixed.geometry.parent.child.recurrence`
as a hypothesis, for the value of `C_rec` at which the contraction factor
`λ_port` is admissible.  Everything the portable proof asks of the recurrence is
its statement at one service length `h` and one scale `r` of the bounded window
`[j_*, T_max]`, so the hypothesis is repackaged here in that form: the two
positivity guards are supplied by the rounded grid together with the window's
finiteness guard, and the four remaining guards are the window's own.

The powered form `e.fixed.geometry.parent.child.powered` follows at once,
with the contraction factor

`β_h = 2^{Q-1}C_{\rm rec}^Q3^{-hQd/2}`

that the centered part of `λ_port` is built from.
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

/-- **The recurrence at one scale of the bounded window.**  The hypothesis of
`p.fixed.geometry.one.grid.propagation` is instantiated at a scale `r` and a service length `h`
with `j_* ≤ r` and `r + h ≤ T_max`. -/
theorem windowed_recurrence [NeZero d] [IsProbabilityMeasure P] {Q Crec : ℝ}
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
    {h r : ℤ} (hh : 1 ≤ h) (hr : jStar ≤ r) (hrT : r + h ≤ TMax) :
    centeredMoment P Q q (r + h) ≤
      ENNReal.ofReal
          (Crec * (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) *
            Real.exp (detIncrement P q r (r + h))) *
        centeredMoment P Q q r +
      ENNReal.ofReal (Crec * gainPhi Q (detIncrement P q r (r + h))) := by
  have hrle : r ≤ TMax := by omega
  have hrh : jStar ≤ r + h := by omega
  exact (hrec P inferInstance hP hunit l q hq r h (le_trans hlj hr) hh
    (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq r (hfin r hr hrle))
    (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq (r + h) (hfin (r + h) hrh hrT))
    (hfin r hr hrle) (hfin (r + h) hrh hrT) (hmom r hr hrle) (hmom (r + h) hrh hrT)).2

/-- **`e.fixed.geometry.parent.child.powered` on the bounded window.**  The
`Q`-th power of the windowed recurrence, with the centered contraction factor of
`λ_port` on the left and an error proportional to `e^{QΔ} - 1` on the right. -/
theorem windowed_powered_recurrence [NeZero d] [IsProbabilityMeasure P] {Q Crec : ℝ}
    (hQ : 1 ≤ Q) (hCrec : 0 ≤ Crec)
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
    {h r : ℤ} (hh : 1 ≤ h) (hr : jStar ≤ r) (hrT : r + h ≤ TMax) :
    centeredMoment P Q q (r + h) ^ Q ≤
      ENNReal.ofReal
          (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
            Real.exp (Q * detIncrement P q r (r + h))) *
        centeredMoment P Q q r ^ Q +
      ENNReal.ofReal
        (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
          (Real.exp (Q * detIncrement P q r (r + h)) - 1)) := by
  have hstep := windowed_recurrence hP hunit hq hlj hfin hmom hrec hh hr hrT
  have hD : 0 ≤ detIncrement P q r (r + h) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj hr) (by omega)
      (hfin r hr (by omega)) (hfin (r + h) (by omega) hrT)
  exact powered_recurrence hQ hCrec hD (Real.rpow_nonneg (by norm_num) _) hstep

/-! ## The contraction factors -/

/-- The centered contraction factor of `p.fixed.geometry.one.grid.propagation` is the sum
of the inherited weight and the factor produced by the powered recurrence. -/
theorem lambdaCen_eq (d : ℕ) (Q a Crec : ℝ) (h : ℤ) :
    lambdaCen d Q a Crec h =
      (3 : ℝ) ^ (-(h : ℝ) * a) +
        2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q := by
  have hpow : ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q =
      (3 : ℝ) ^ (-(h : ℝ) * Q * (d : ℝ) / 2) := by
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [lambdaCen, hpow]

/-- The inherited weight is at most the portable contraction factor. -/
theorem rpow_le_lambdaPort (d : ℕ) (Q a Crec : ℝ) (h : ℤ) :
    (3 : ℝ) ^ (-(h : ℝ) * a) ≤ lambdaPort d Q a Crec h :=
  le_max_right _ _

/-- The centered contraction factor is at most the portable contraction
factor. -/
theorem lambdaCen_le_lambdaPort (d : ℕ) (Q a Crec : ℝ) (h : ℤ) :
    lambdaCen d Q a Crec h ≤ lambdaPort d Q a Crec h :=
  le_max_left _ _

end Window

end

end PortableHistory
end HighContrast
end Homogenization
