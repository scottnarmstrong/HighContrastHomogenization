/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Service
import HCPoly.Provider.PortableHistory.Geometric

/-!
# The nonlinear row over one service length

The contraction of the nonlinear row over one service length is the third of the
row estimates that add up to the service display of
`p.fixed.geometry.one.grid.propagation`:

`N_{T+h} ≤ 3^{-ha}e^{QΔ̂_h^q(T)}N_T + C(a,h)(e^{QΔ̂_h^q(T)} - 1)`,

where `N_T = ∑_{j=b}^{T-1}3^{-a(T-1-j)}𝔥_Q(P_{j,T}^q)` is the last row of
`e.scale.selection.complete.profile`.

The old scales are transported from `T` to `T + h` by the exponential transport
of the mean penalty: their principal parts carry the
factor `3^{-ha}e^{QΔ̂_h^q(T)}`, and their additive parts form a geometric sum
bounded by `(1 - 3^{-a})^{-1}`.  The `h` fresh scales start at
`P_{j,j}^q = I`, so the same transport bounds each of them by
`e^{QΔ̂_h^q(T)} - 1` alone.  Every term is a nonnegative real, so the row
estimate is proved over the reals and read back into `ℝ≥0∞`.
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

/-- **The contraction of the nonlinear row over one service length, on the
reals.**  The nonlinear row of the profile contracts by `3^{-ha}e^{QΔ̂_h^q(T)}`
over one service length, at the cost of a bounded geometric sum times
`e^{QΔ̂_h^q(T)} - 1`. -/
theorem nonlinear_service_real [NeZero d] [IsProbabilityMeasure P] {Q a : ℝ}
    (hQ : 0 ≤ Q) (ha : 0 < a)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b h T : ℤ} (hh : 1 ≤ h) (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T + h ≤ TMax) :
    ∑ j ∈ Finset.Ico b (T + h),
        (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (T + h)) ≤
      (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
          (∑ j ∈ Finset.Ico b T,
            (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)) +
        (1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ)) * (Real.exp (Q * synchCharge P q h T) - 1) := by
  have hbTle : b ≤ T := by omega
  have hTTh : T ≤ T + h := by omega
  have hcharge0 := synchCharge_nonneg hP hq hlj hfin hh (by omega) hT
  have hE1 : (1 : ℝ) ≤ Real.exp (Q * synchCharge P q h T) :=
    Real.one_le_exp (mul_nonneg hQ hcharge0)
  have hha : -(h : ℝ) * a ≤ 0 := by
    have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    nlinarith only [h1, ha]
  have hgeomw : (3 : ℝ) ^ (-(h : ℝ) * a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hha
  have hgeomw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(h : ℝ) * a) := Real.rpow_nonneg (by norm_num) _
  -- the old scales
  have hold : ∑ j ∈ Finset.Ico b T,
      (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) *
        frakH Q (relMean P q j (T + h)) ≤
      (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
          (∑ j ∈ Finset.Ico b T,
            (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)) +
        (Real.exp (Q * synchCharge P q h T) - 1) * (1 / (1 - (3 : ℝ) ^ (-a))) := by
    have hterm : ∀ j ∈ Finset.Ico b T,
        (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) *
            frakH Q (relMean P q j (T + h)) ≤
          (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
              ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)) +
            (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              (Real.exp (Q * synchCharge P q h T) - 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hsplit : (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) =
          (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
        congr 1
        push_cast
        ring
      have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) :=
        Real.rpow_nonneg (by norm_num) _
      have htrans := frakH_transport_exponential hQ hP hq hlj hfin (j := j) (s := T)
        (t := T + h) (by omega) (by omega) (by omega) hT
      have hcharge := detIncrement_le_synchCharge_step hP hq hlj hfin hh (by omega) hT
      have hexpmono : Real.exp (Q * detIncrement P q T (T + h)) ≤
          Real.exp (Q * synchCharge P q h T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcharge hQ)
      have hFT0 := frakH_relMean_nonneg hQ hP hq hlj hfin (j := j) (T := T)
        (by omega) (by omega) (by omega)
      have hbound : frakH Q (relMean P q j (T + h)) ≤
          Real.exp (Q * synchCharge P q h T) * frakH Q (relMean P q j T) +
            (Real.exp (Q * synchCharge P q h T) - 1) := by
        have hmul : Real.exp (Q * detIncrement P q T (T + h)) * frakH Q (relMean P q j T) ≤
            Real.exp (Q * synchCharge P q h T) * frakH Q (relMean P q j T) :=
          mul_le_mul_of_nonneg_right hexpmono hFT0
        linarith only [htrans, hmul, hexpmono]
      rw [hsplit, mul_assoc]
      have hstep : (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (T + h)) ≤
          (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            (Real.exp (Q * synchCharge P q h T) * frakH Q (relMean P q j T) +
              (Real.exp (Q * synchCharge P q h T) - 1)) :=
        mul_le_mul_of_nonneg_left hbound hw0
      have hslack : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
          (Real.exp (Q * synchCharge P q h T) - 1) :=
        mul_nonneg hw0 (by linarith only [hE1])
      nlinarith only [hstep, hslack, hgeomw, hgeomw0, hw0]
    have hsum := Finset.sum_le_sum hterm
    have hdistr : ∑ j ∈ Finset.Ico b T,
        ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)) +
          (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            (Real.exp (Q * synchCharge P q h T) - 1)) =
        (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
            (∑ j ∈ Finset.Ico b T,
              (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)) +
          (∑ j ∈ Finset.Ico b T, (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ)))) *
            (Real.exp (Q * synchCharge P q h T) - 1) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hdistr] at hsum
    have hgeom := sum_geom_Ico_le ha b T
    have hgeomsum : (∑ j ∈ Finset.Ico b T, (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ)))) *
        (Real.exp (Q * synchCharge P q h T) - 1) ≤
        (Real.exp (Q * synchCharge P q h T) - 1) * (1 / (1 - (3 : ℝ) ^ (-a))) := by
      have hE0 : (0 : ℝ) ≤ Real.exp (Q * synchCharge P q h T) - 1 := by linarith only [hE1]
      nlinarith only [hgeom, hE0]
    linarith only [hsum, hgeomsum]
  -- the fresh scales
  have hfresh : ∑ j ∈ Finset.Ico T (T + h),
      (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) *
        frakH Q (relMean P q j (T + h)) ≤
      (h : ℝ) * (Real.exp (Q * synchCharge P q h T) - 1) := by
    have hterm : ∀ j ∈ Finset.Ico T (T + h),
        (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (T + h)) ≤
          Real.exp (Q * synchCharge P q h T) - 1 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hjr : (j : ℝ) ≤ ((T + h : ℤ) : ℝ) - 1 := by
        have : (j : ℤ) ≤ (T + h : ℤ) - 1 := by omega
        have hcast : ((j : ℤ) : ℝ) ≤ (((T + h : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at hcast ⊢
        linarith only [hcast]
      have hexp0 : -a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ)) ≤ 0 := by
        have hnn : (0 : ℝ) ≤ ((T + h : ℤ) : ℝ) - 1 - (j : ℝ) := by linarith only [hjr]
        nlinarith only [hnn, ha]
      have hw : (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp0
      have hF0 := frakH_relMean_nonneg hQ hP hq hlj hfin (j := j) (T := T + h)
        (by omega) (by omega) hT
      have hFle : frakH Q (relMean P q j (T + h)) ≤ Real.exp (Q * synchCharge P q h T) - 1 := by
        have hdet := one_add_frakH_le_exp hQ hP hq hlj hfin (s := j) (t := T + h)
          (by omega) (by omega) hT
        have hcharge := detIncrement_le_synchCharge_of_le (s := j) hP hq hlj hfin hh
          (by omega) (by omega) (by omega) hT
        have hexpmono : Real.exp (Q * detIncrement P q j (T + h)) ≤
            Real.exp (Q * synchCharge P q h T) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcharge hQ)
        linarith only [hdet, hexpmono]
      nlinarith only [hw, hF0, hFle]
    have hcard : (Finset.Ico T (T + h)).card = h.toNat := by
      rw [Int.card_Ico]
      congr 1
      ring
    have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (le_trans zero_le_one hh)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [hcard, nsmul_eq_mul, hcast] at hsum
    exact hsum
  have hunion : Finset.Ico b T ∪ Finset.Ico T (T + h) = Finset.Ico b (T + h) :=
    Finset.Ico_union_Ico_eq_Ico hbTle hTTh
  have hdisj : Disjoint (Finset.Ico b T) (Finset.Ico T (T + h)) :=
    Finset.Ico_disjoint_Ico_consecutive b T (T + h)
  rw [← hunion, Finset.sum_union hdisj]
  linarith only [hold, hfresh]

/-- **The contraction of the nonlinear row over one service length.**  The
nonlinear row of `e.scale.selection.complete.profile` contracts by
`3^{-ha}e^{QΔ̂_h^q(T)}` over one service length, with an additive error
proportional to `e^{QΔ̂_h^q(T)} - 1`. -/
theorem nonlinear_service [NeZero d] [IsProbabilityMeasure P] {Q a : ℝ}
    (hQ : 0 ≤ Q) (ha : 0 < a)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b h T : ℤ} (hh : 1 ≤ h) (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T + h ≤ TMax) :
    ∑ j ∈ Finset.Ico b (T + h),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (T + h))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) *
          (∑ j ∈ Finset.Ico b T,
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j T))) +
        ENNReal.ofReal ((1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ)) *
          (Real.exp (Q * synchCharge P q h T) - 1)) := by
  have hcharge0 := synchCharge_nonneg hP hq hlj hfin hh (by omega) hT
  have hE1 : (1 : ℝ) ≤ Real.exp (Q * synchCharge P q h T) :=
    Real.one_le_exp (mul_nonneg hQ hcharge0)
  have hnew : ∀ j ∈ Finset.Ico b (T + h),
      (0 : ℝ) ≤ (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - 1 - (j : ℝ))) *
        frakH Q (relMean P q j (T + h)) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (frakH_relMean_nonneg hQ hP hq hlj hfin (j := j) (T := T + h) (by omega) (by omega) hT)
  have hcur : ∀ j ∈ Finset.Ico b T,
      (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (frakH_relMean_nonneg hQ hP hq hlj hfin (j := j) (T := T) (by omega) (by omega) (by omega))
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico b T,
      (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T) :=
    Finset.sum_nonneg hcur
  have hcoef0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
  have hconst0 : (0 : ℝ) ≤ (1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ)) *
      (Real.exp (Q * synchCharge P q h T) - 1) := by
    have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by
      have := geom_ratio_lt_one ha
      linarith only [this]
    have hh0 : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans zero_le_one hh
    have hinv : (0 : ℝ) < 1 / (1 - (3 : ℝ) ^ (-a)) := by positivity
    exact mul_nonneg (by linarith only [hinv, hh0]) (by linarith only [hE1])
  rw [← ENNReal.ofReal_sum_of_nonneg hnew, ← ENNReal.ofReal_sum_of_nonneg hcur,
    ← ENNReal.ofReal_mul hcoef0, ← ENNReal.ofReal_add (mul_nonneg hcoef0 hsum0) hconst0]
  exact ENNReal.ofReal_le_ofReal (nonlinear_service_real hQ ha hP hq hlj hfin hh hb hbT hT)

end Window

end

end PortableHistory
end HighContrast
end Homogenization
