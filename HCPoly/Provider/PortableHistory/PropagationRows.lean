/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Propagation
import HCPoly.Provider.PortableHistory.Geometric

/-!
# The old rows of the propagation estimate

Propagating the profile from `T` to `T+L` transports the three rows of
`e.scale.selection.complete.profile` that are already present at `T`.  Every one of
them carries the geometric factor `3^{-aL} ≤ 1` and the exponential
`e^{QD}` of `D = Δ_{T,T+L}^q`:

* the inherited row, through
  `1 + 𝔥_Q(P_{b,T+L}^q) ≤ (1 + 𝔥_Q(P_{b,T}^q))e^{QD}`, which is the nonlinear
  and determinant transports at `s = T`;
* the old centered row, through `e^{QΔ_{j,T+L}^q} = e^{QΔ_{j,T}^q}e^{QD}`;
* the old nonlinear row, through
  `𝔥_Q(P_{j,T+L}^q) ≤ e^{QD}𝔥_Q(P_{j,T}^q) + (e^{QD} - 1)`, whose additive parts
  form the bounded geometric sum `(1-3^{-a})^{-1}`.

The `L` fresh nonlinear terms are the ones the checkpoint estimate already
bounds, read at the checkpoint `T`.
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

/-! ## The inherited row -/

/-- The inherited row of the profile is transported from `T` to `T+L` at the
cost of `e^{QD}`. -/
theorem propagation_inherited [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ} (hQ : 0 ≤ Q)
    (ha : 0 < a)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b L T : ℤ} (hL : 1 ≤ L) (hb : jStar ≤ b) (hbT : b ≤ T) (hTL : T + L ≤ TMax) :
    ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b (T + L)))) *
        portableHistory P Q a rhoMax q jStar b ≤
      ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
        (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            (1 + frakH Q (relMean P q b T))) *
          portableHistory P Q a rhoMax q jStar b) := by
  have hgain := one_add_frakH_mul_le hQ hP hq hlj hfin (j := b) (s := T) (t := T + L) hb hbT
    (by omega) hTL
  have hexp := one_add_frakH_le_exp hQ hP hq hlj hfin (s := T) (t := T + L)
    (le_trans hb hbT) (by omega) hTL
  have hT0 : (0 : ℝ) ≤ 1 + frakH Q (relMean P q b T) := by
    have := frakH_relMean_nonneg hQ hP hq hlj hfin (j := b) (T := T) hb hbT (by omega)
    linarith only [this]
  have hL0 : (0 : ℝ) ≤ 1 + frakH Q (relMean P q b (T + L)) := by
    have := frakH_relMean_nonneg hQ hP hq hlj hfin (j := b) (T := T + L) hb (by omega) hTL
    linarith only [this]
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hsplit : (3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (b : ℝ))) =
      (3 : ℝ) ^ (-(L : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hwle : (3 : ℝ) ^ (-(L : ℝ) * a) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    nlinarith only [hLr, ha]
  have hcoeff : (3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (b : ℝ))) *
      (1 + frakH Q (relMean P q b (T + L))) ≤
      Real.exp (Q * detIncrement P q T (T + L)) *
        ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b T))) := by
    rw [hsplit, mul_assoc]
    calc (3 : ℝ) ^ (-(L : ℝ) * a) *
          ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b (T + L))))
        ≤ 1 * ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            (1 + frakH Q (relMean P q b (T + L)))) :=
          mul_le_mul_of_nonneg_right hwle (mul_nonneg hw0 hL0)
      _ = (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b (T + L))) :=
          one_mul _
      _ ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            ((1 + frakH Q (relMean P q b T)) *
              Real.exp (Q * detIncrement P q T (T + L))) :=
          mul_le_mul_of_nonneg_left (le_trans hgain (mul_le_mul_of_nonneg_left hexp hT0)) hw0
      _ = Real.exp (Q * detIncrement P q T (T + L)) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b T))) := by
          ring
  calc ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (b : ℝ))) *
        (1 + frakH Q (relMean P q b (T + L)))) * portableHistory P Q a rhoMax q jStar b
      ≤ ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b T)))) *
          portableHistory P Q a rhoMax q jStar b :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl
    _ = ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
              (1 + frakH Q (relMean P q b T))) *
            portableHistory P Q a rhoMax q jStar b) :=
        (ofReal_mul_ofReal_mul (Real.exp_pos _).le _ _).symm

/-! ## The old centered row -/

/-- The centered row of the profile is transported from `T` to `T+L` at the cost
of `e^{QD}`. -/
theorem propagation_centered_old [NeZero d] {Q a : ℝ} (ha : 0 < a)
    {b L T : ℤ} (hL : 1 ≤ L) :
    ∑ j ∈ Finset.Icc (b + 1) T,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + L))) *
          centeredMoment P Q q j ^ Q ≤
      ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
        ∑ j ∈ Finset.Icc (b + 1) T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
              Real.exp (Q * detIncrement P q j T)) *
            centeredMoment P Q q j ^ Q := by
  have hwle : (3 : ℝ) ^ (-(L : ℝ) * a) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    nlinarith only [hLr, ha]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hsplit : (3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ))) =
      (3 : ℝ) ^ (-(L : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hexp : Real.exp (Q * detIncrement P q j (T + L)) =
      Real.exp (Q * detIncrement P q T (T + L)) * Real.exp (Q * detIncrement P q j T) := by
    rw [← Real.exp_add, detIncrement_add P q j T (T + L)]
    ring_nf
  have hcoeff : (3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ))) *
      Real.exp (Q * detIncrement P q j (T + L)) ≤
      Real.exp (Q * detIncrement P q T (T + L)) *
        ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) * Real.exp (Q * detIncrement P q j T)) := by
    rw [hsplit, hexp, mul_assoc]
    calc (3 : ℝ) ^ (-(L : ℝ) * a) *
          ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
            (Real.exp (Q * detIncrement P q T (T + L)) *
              Real.exp (Q * detIncrement P q j T)))
        ≤ 1 * ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
            (Real.exp (Q * detIncrement P q T (T + L)) *
              Real.exp (Q * detIncrement P q j T))) :=
          mul_le_mul_of_nonneg_right hwle
            (mul_nonneg hw0 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
      _ = Real.exp (Q * detIncrement P q T (T + L)) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
              Real.exp (Q * detIncrement P q j T)) := by ring
  refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl) ?_
  exact le_of_eq (ofReal_mul_ofReal_mul (Real.exp_pos _).le _ _).symm

/-! ## The old nonlinear row -/

/-- The nonlinear row of the profile is transported from `T` to `T+L` at the cost
of `e^{QD}` and a bounded geometric sum times `e^{QD} - 1`. -/
theorem propagation_nonlinear_old [NeZero d] [IsProbabilityMeasure P] {Q a : ℝ} (hQ : 0 ≤ Q)
    (ha : 0 < a)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b L T : ℤ} (hL : 1 ≤ L) (hb : jStar ≤ b) (hbT : b ≤ T) (hTL : T + L ≤ TMax) :
    ∑ j ∈ Finset.Ico b T,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (T + L))) ≤
      ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
          ∑ j ∈ Finset.Ico b T,
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j T)) +
        ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
          (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
  have hD0 : 0 ≤ detIncrement P q T (T + L) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj (le_trans hb hbT)) (by omega)
      (hfin T (le_trans hb hbT) (by omega)) (hfin (T + L) (by omega) hTL)
  have hED1 : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q T (T + L)) :=
    Real.one_le_exp (mul_nonneg hQ hD0)
  have hED0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q T (T + L)) - 1 := by linarith only [hED1]
  have hwle : (3 : ℝ) ^ (-(L : ℝ) * a) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    nlinarith only [hLr, ha]
  have hterm : ∀ j ∈ Finset.Ico b T,
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (T + L))) ≤
        ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j T)) +
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hsplit : (3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - 1 - (j : ℝ))) =
        (3 : ℝ) ^ (-(L : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    have htrans := frakH_transport_exponential hQ hP hq hlj hfin (j := j) (s := T) (t := T + L)
      (by omega) (by omega) (by omega) hTL
    have hF0 := frakH_relMean_nonneg hQ hP hq hlj hfin (j := j) (T := T + L)
      (by omega) (by omega) hTL
    have hFT0 := frakH_relMean_nonneg hQ hP hq hlj hfin (j := j) (T := T)
      (by omega) (by omega) (by omega)
    have hreal : (3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
        frakH Q (relMean P q j (T + L)) ≤
        Real.exp (Q * detIncrement P q T (T + L)) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)) +
          (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            (Real.exp (Q * detIncrement P q T (T + L)) - 1) := by
      rw [hsplit, mul_assoc]
      calc (3 : ℝ) ^ (-(L : ℝ) * a) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j (T + L)))
          ≤ 1 * ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j (T + L))) :=
            mul_le_mul_of_nonneg_right hwle (mul_nonneg hw0 hF0)
        _ = (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j (T + L)) :=
            one_mul _
        _ ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              (Real.exp (Q * detIncrement P q T (T + L)) * frakH Q (relMean P q j T) +
                (Real.exp (Q * detIncrement P q T (T + L)) - 1)) :=
            mul_le_mul_of_nonneg_left htrans hw0
        _ = Real.exp (Q * detIncrement P q T (T + L)) *
              ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)) +
            (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1) := by ring
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (mul_nonneg hw0 hFT0))
      (mul_nonneg hw0 hED0)]
    exact add_le_add (le_of_eq (ENNReal.ofReal_mul (Real.exp_pos _).le)) le_rfl
  have hconst : ∑ j ∈ Finset.Ico b T,
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
        (Real.exp (Q * detIncrement P q T (T + L)) - 1)) ≤
      ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
        (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hED0)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_geom_Ico_le ha b T) hED0
  calc ∑ j ∈ Finset.Ico b T,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (T + L)))
      ≤ ∑ j ∈ Finset.Ico b T,
          (ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
              ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
                frakH Q (relMean P q j T)) +
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1))) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
          (∑ j ∈ Finset.Ico b T,
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j T))) +
        ∑ j ∈ Finset.Ico b T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
          (∑ j ∈ Finset.Ico b T,
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j T))) +
        ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
          (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := add_le_add le_rfl hconst

end Window

end

end PortableHistory
end HighContrast
end Homogenization
