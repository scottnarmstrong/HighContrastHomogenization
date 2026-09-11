/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Charge
import HCPoly.Provider.PortableHistory.GainPower

/-!
# The inherited row over one service length

The contraction of the carried initial-history term is the first of the three
row estimates that add up to the service display of
`p.fixed.geometry.one.grid.propagation`:

`I_{T+h} ≤ 3^{-ha}e^{QΔ̂_h^q(T)}I_T`,

where `I_T = 3^{-a(T-b)}(1 + 𝔥_Q(P_{b,T}^q))𝓗_q(b)` is the inherited row of
`e.scale.selection.complete.profile`.

Its two ingredients are already available: the geometric weight splits as
`3^{-a(T+h-b)} = 3^{-ha}3^{-a(T-b)}`, and the gain at the later terminal scale
is bounded through `e.two.grid.mean.split` and the determinant bound for the
mean penalty by `e^{QΔ_{T,T+h}^q}` times the gain at `T`.  The charge dominates
that increment, which is `e.scale.selection.synchronized.loss.lower` together
with the positivity of the increment over `[T+1-h, T]`.
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

/-- The increment from any scale of the covered span to the end of the service
length is dominated by the synchronized charge. -/
theorem detIncrement_le_synchCharge_of_le [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h T s : ℤ} (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hs : T + 1 - h ≤ s)
    (hsT : s ≤ T + h) (hhigh : T + h ≤ TMax) :
    detIncrement P q s (T + h) ≤ synchCharge P q h T := by
  have hspan := detIncrement_le_synchCharge hP hq hlj hfin hh hlow hhigh
  have hsplit := detIncrement_add P q (T + 1 - h) s (T + h)
  have hleft := Recurrence.detIncrement_nonneg (p := s) hP hq (le_trans hlj hlow) hs
    (hfin (T + 1 - h) hlow (by omega)) (hfin s (by omega) (by omega))
  linarith only [hspan, hsplit, hleft]

/-- The increment over one service length is dominated by the synchronized
charge. -/
theorem detIncrement_le_synchCharge_step [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h T : ℤ} (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hhigh : T + h ≤ TMax) :
    detIncrement P q T (T + h) ≤ synchCharge P q h T :=
  detIncrement_le_synchCharge_of_le hP hq hlj hfin hh hlow (by omega) (by omega) hhigh

/-- **The contraction of the carried initial-history term, on the
coefficients.**  The weight of the inherited row contracts by `3^{-ha}` over one
service length, at the cost of the exponential of the charge. -/
theorem inherited_service_coeff [NeZero d] [IsProbabilityMeasure P] {Q a : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b h T : ℤ} (hh : 1 ≤ h) (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T + h ≤ TMax) :
    (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b (T + h))) ≤
      (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
        ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b T))) := by
  have hbTle : b ≤ T := by omega
  have hTh : T ≤ T + h := by omega
  have hTmax : T ≤ TMax := by omega
  -- the geometric weight splits
  have hsplit : (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (b : ℝ))) =
      (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    push_cast
    ring
  -- the gain at the later terminal scale
  have hgain := one_add_frakH_mul_le hQ hP hq hlj hfin (j := b) (s := T) (t := T + h)
    hb hbTle hTh hT
  have hexp := one_add_frakH_le_exp hQ hP hq hlj hfin (s := T) (t := T + h)
    (le_trans hb hbTle) hTh hT
  have hcharge := detIncrement_le_synchCharge_step hP hq hlj hfin hh (by omega) hT
  have hexpmono : Real.exp (Q * detIncrement P q T (T + h)) ≤
      Real.exp (Q * synchCharge P q h T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcharge hQ)
  have hbT0 : 0 ≤ 1 + frakH Q (relMean P q b T) := by
    have := frakH_relMean_nonneg hQ hP hq hlj hfin hb hbTle hTmax
    linarith only [this]
  have hchain : 1 + frakH Q (relMean P q b (T + h)) ≤
      (1 + frakH Q (relMean P q b T)) * Real.exp (Q * synchCharge P q h T) := by
    refine le_trans hgain (mul_le_mul_of_nonneg_left (le_trans hexp hexpmono) hbT0)
  have hweight : (0 : ℝ) ≤ (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
  rw [hsplit]
  calc (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
        (1 + frakH Q (relMean P q b (T + h)))
      ≤ (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
          ((1 + frakH Q (relMean P q b T)) * Real.exp (Q * synchCharge P q h T)) :=
        mul_le_mul_of_nonneg_left hchain hweight
    _ = (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
          ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b T))) := by
        ring

/-- **The contraction of the carried initial-history term.**  The inherited row
of the profile contracts by `3^{-ha}e^{QΔ̂_h^q(T)}` over one service length. -/
theorem inherited_service [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b h T : ℤ} (hh : 1 ≤ h) (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T + h ≤ TMax) :
    ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b (T + h)))) *
        portableHistory P Q a rhoMax q jStar b ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) *
        (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            (1 + frakH Q (relMean P q b T))) *
          portableHistory P Q a rhoMax q jStar b) := by
  have hcoeff := inherited_service_coeff (a := a) hQ hP hq hlj hfin hh hb hbT hT
  have hmul : ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (b : ℝ))) *
        (1 + frakH Q (relMean P q b (T + h)))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) *
        ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b T))) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hcoeff
  calc ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (b : ℝ))) *
        (1 + frakH Q (relMean P q b (T + h)))) * portableHistory P Q a rhoMax q jStar b
      ≤ (ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) *
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            (1 + frakH Q (relMean P q b T)))) * portableHistory P Q a rhoMax q jStar b :=
        mul_le_mul' hmul (le_refl _)
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
              (1 + frakH Q (relMean P q b T))) *
            portableHistory P Q a rhoMax q jStar b) := by
        rw [mul_assoc]


/-- The synchronized charge is nonnegative on the covered span. -/
theorem synchCharge_nonneg [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h T : ℤ} (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hhigh : T + h ≤ TMax) :
    0 ≤ synchCharge P q h T := by
  have hstep := detIncrement_le_synchCharge_step hP hq hlj hfin hh hlow hhigh
  have hnn := Recurrence.detIncrement_nonneg (p := T + h) hP hq (le_trans hlj (by omega)) (by omega)
    (hfin T (by omega) (by omega)) (hfin (T + h) (by omega) hhigh)
  linarith only [hstep, hnn]

end Window

end

end PortableHistory
end HighContrast
end Homogenization
