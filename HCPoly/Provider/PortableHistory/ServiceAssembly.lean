/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.CenteredService

/-!
# The service estimate

`e.fixed.geometry.profile.contraction` is the contraction of the portable profile over
one service length:

`𝒫_q(T+h;b) ≤ λ_port e^{QΔ̂_h^q(T)}𝒫_q(T;b) + C(e^{QΔ̂_h^q(T)} - 1)`.

It is the sum of the three row estimates.  The inherited row and the nonlinear
row each carry the inherited weight `3^{-ha}`, and the centered row carries
`λ_cen = 3^{-ha} + β_h`; the portable contraction factor `λ_port` is the maximum
of the two, so a single factor serves all three rows.  The additive error is the
bounded geometric sum of the nonlinear row together with the `h` fresh centered
errors, and every summand is proportional to `e^{QΔ̂_h^q(T)} - 1`: no
scale-independent positive term survives.

The constant is exhibited: `C = (1-3^{-a})^{-1} + h + h2^{Q-1}C_{\rm rec}^Q2^Q`.
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

/-! ## The centered row -/

/-- **The contraction of the fluctuation terms over one service step.**  The
centered row of `e.scale.selection.complete.profile` contracts by
`λ_cen e^{QΔ̂_h^q(T)}` over one service length, with an additive error
proportional to `e^{QΔ̂_h^q(T)} - 1`. -/
theorem centered_service [NeZero d] [IsProbabilityMeasure P] {Q a Crec : ℝ}
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
    {b h T : ℤ} (hh : 1 ≤ h) (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T + h ≤ TMax) :
    ∑ j ∈ Finset.Icc (b + 1) (T + h),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + h))) *
          centeredMoment P Q q j ^ Q ≤
      ENNReal.ofReal (lambdaCen d Q a Crec h * Real.exp (Q * synchCharge P q h T)) *
          ∑ j ∈ Finset.Icc (b + 1) T,
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
                Real.exp (Q * detIncrement P q j T)) *
              centeredMoment P Q q j ^ Q +
        ENNReal.ofReal ((h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
          (Real.exp (Q * synchCharge P q h T) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hunion : Finset.Icc (b + 1) T ∪ Finset.Icc (T + 1) (T + h) =
      Finset.Icc (b + 1) (T + h) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc (b + 1) T) (Finset.Icc (T + 1) (T + h)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    omega
  have hsplit : ENNReal.ofReal (lambdaCen d Q a Crec h * Real.exp (Q * synchCharge P q h T)) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) +
        ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
          Real.exp (Q * synchCharge P q h T)) := by
    rw [lambdaCen_eq, add_mul,
      ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [← hunion, Finset.sum_union hdisj, hsplit, add_mul]
  refine le_trans (add_le_add (centered_service_old hQ0 hP hq hlj hfin hh hb hbT hT)
    (centered_service_new hQ ha hCrec hP hunit hq hlj hfin hmom hrec hh hb hbT hT))
    (le_of_eq (add_assoc _ _ _).symm)

/-! ## The service estimate -/

/-- **`e.fixed.geometry.profile.contraction`.**  The portable profile contracts by
`λ_port e^{QΔ̂_h^q(T)}` over one service length, with an additive error
proportional to `e^{QΔ̂_h^q(T)} - 1` and no scale-independent positive term. -/
theorem portableProfile_service [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax Crec : ℝ}
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
    {b h T : ℤ} (hh : 1 ≤ h) (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T + h ≤ TMax) :
    portableProfile P Q a rhoMax q jStar b (T + h) ≤
      ENNReal.ofReal (lambdaPort d Q a Crec h * Real.exp (Q * synchCharge P q h T)) *
          portableProfile P Q a rhoMax q jStar b T +
        ENNReal.ofReal
          ((1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ) + (h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q)) *
            (Real.exp (Q * synchCharge P q h T) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hE0 : (0 : ℝ) ≤ Real.exp (Q * synchCharge P q h T) := (Real.exp_pos _).le
  have hEge : (1 : ℝ) ≤ Real.exp (Q * synchCharge P q h T) :=
    Real.one_le_exp (mul_nonneg hQ0 (synchCharge_nonneg hP hq hlj hfin hh (by omega) hT))
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans zero_le_one hh
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by
    have := geom_ratio_lt_one ha
    linarith only [this]
  have hcN0 : (0 : ℝ) ≤ (1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ)) *
      (Real.exp (Q * synchCharge P q h T) - 1) := by
    have hinv : (0 : ℝ) < 1 / (1 - (3 : ℝ) ^ (-a)) := by positivity
    exact mul_nonneg (by linarith only [hinv, hh0]) (by linarith only [hEge])
  have hcV0 : (0 : ℝ) ≤ (h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
      (Real.exp (Q * synchCharge P q h T) - 1) := by
    have hfac : (0 : ℝ) ≤ (h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) := by positivity
    exact mul_nonneg hfac (by linarith only [hEge])
  -- the three rows, each with the portable contraction factor
  have hgeo : ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) ≤
      ENNReal.ofReal (lambdaPort d Q a Crec h * Real.exp (Q * synchCharge P q h T)) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (rpow_le_lambdaPort d Q a Crec h) hE0)
  have hcen : ENNReal.ofReal (lambdaCen d Q a Crec h * Real.exp (Q * synchCharge P q h T)) ≤
      ENNReal.ofReal (lambdaPort d Q a Crec h * Real.exp (Q * synchCharge P q h T)) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (lambdaCen_le_lambdaPort d Q a Crec h) hE0)
  have hI := le_trans (inherited_service (rhoMax := rhoMax) hQ0 hP hq hlj hfin hh hb hbT hT)
    (mul_le_mul' hgeo le_rfl)
  have hV := le_trans (centered_service hQ ha hCrec hP hunit hq hlj hfin hmom hrec hh hb hbT hT)
    (add_le_add (mul_le_mul' hcen le_rfl) le_rfl)
  have hN := le_trans (nonlinear_service hQ0 ha hP hq hlj hfin hh hb hbT hT)
    (add_le_add (mul_le_mul' hgeo le_rfl) le_rfl)
  have herr : ENNReal.ofReal ((h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
        (Real.exp (Q * synchCharge P q h T) - 1)) +
      ENNReal.ofReal ((1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ)) *
        (Real.exp (Q * synchCharge P q h T) - 1)) =
      ENNReal.ofReal
        ((1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ) + (h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q)) *
          (Real.exp (Q * synchCharge P q h T) - 1)) := by
    rw [← ENNReal.ofReal_add hcV0 hcN0]
    congr 1
    ring
  simp only [portableProfile]
  refine le_trans (add_le_add (add_le_add hI hV) hN) (le_of_eq ?_)
  rw [← herr]
  ring

end Window

end

end PortableHistory
end HighContrast
end Homogenization
