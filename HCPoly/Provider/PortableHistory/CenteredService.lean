/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.ServiceNonlinear
import HCPoly.Provider.PortableHistory.WindowedRecurrence

/-!
# The two halves of the centered row over one service length

The contraction of the fluctuation terms over one service step estimates the
middle row
`V_T = ∑_{j=b+1}^T 3^{-a(T-j)}e^{QΔ_{j,T}^q}(v_j^q)^Q` of
`e.scale.selection.complete.profile` over one service length.  Its old terms are
those of `V_T` multiplied by `3^{-ha}e^{QΔ_{T,T+h}^q}`, an increment the charge
dominates.  The `h` fresh indices `T < j ≤ T+h` are handled by
`e.fixed.geometry.parent.child.powered` at the predecessor `j - h`; those
predecessors are distinct elements of `{T+1-h, …, T}`, which the service
hypothesis `T ≥ b+h` places inside the range of `V_T`, and the identity
`e^{QΔ_{j,T+h}^q}(e^{QΔ_{j-h,j}^q} - 1) = e^{QΔ_{j-h,T+h}^q} - e^{QΔ_{j,T+h}^q}`
with the charge coverage bounds each fresh error by `e^{QΔ̂_h^q(T)} - 1`.  The
powered moments may be infinite, so the estimate is carried out in `ℝ≥0∞`.
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

/-! ## The old terms of the centered row -/

/-- The terms of `V_{T+h}` at the scales already present in `V_T` carry the
factor `3^{-ha}e^{QΔ̂_h^q(T)}`. -/
theorem centered_service_old [NeZero d] [IsProbabilityMeasure P] {Q a : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b h T : ℤ} (hh : 1 ≤ h) (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T + h ≤ TMax) :
    ∑ j ∈ Finset.Icc (b + 1) T,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + h))) *
          centeredMoment P Q q j ^ Q ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T)) *
        ∑ j ∈ Finset.Icc (b + 1) T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
              Real.exp (Q * detIncrement P q j T)) *
            centeredMoment P Q q j ^ Q := by
  have hcharge := detIncrement_le_synchCharge_step hP hq hlj hfin hh (by omega) hT
  have hcoef0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hsplit : (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (j : ℝ))) =
      (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hmulQ : Q * detIncrement P q j (T + h) =
      Q * detIncrement P q j T + Q * detIncrement P q T (T + h) := by
    rw [detIncrement_add P q j T (T + h)]
    ring
  have hexp : Real.exp (Q * detIncrement P q j (T + h)) ≤
      Real.exp (Q * synchCharge P q h T) * Real.exp (Q * detIncrement P q j T) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hle := mul_le_mul_of_nonneg_left hcharge hQ
    linarith only [hmulQ, hle]
  have hreal : (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (j : ℝ))) *
      Real.exp (Q * detIncrement P q j (T + h)) ≤
      (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
        ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) * Real.exp (Q * detIncrement P q j T)) := by
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    rw [hsplit, mul_assoc]
    calc (3 : ℝ) ^ (-(h : ℝ) * a) *
          ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) * Real.exp (Q * detIncrement P q j (T + h)))
        = (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + h)) := by ring
      _ ≤ (3 : ℝ) ^ (-(h : ℝ) * a) * (3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
            (Real.exp (Q * synchCharge P q h T) * Real.exp (Q * detIncrement P q j T)) :=
          mul_le_mul_of_nonneg_left hexp hw0
      _ = (3 : ℝ) ^ (-(h : ℝ) * a) * Real.exp (Q * synchCharge P q h T) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) * Real.exp (Q * detIncrement P q j T)) := by
          ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul hcoef0]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-! ## The fresh terms of the centered row -/

/-- The fresh error of one new centered scale: the terminal weight turns
`e^{QΔ_{r,r+h}} - 1` into `e^{QΔ_{r,T+h}} - e^{QΔ_{r+h,T+h}}`, which the charge
coverage bounds by `e^{QΔ̂_h^q(T)} - 1`. -/
theorem exp_mul_exp_sub_one_le [NeZero d] [IsProbabilityMeasure P] {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h T r : ℤ} (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hr : T + 1 - h ≤ r) (hrT : r ≤ T)
    (hT : T + h ≤ TMax) :
    Real.exp (Q * detIncrement P q (r + h) (T + h)) *
        (Real.exp (Q * detIncrement P q r (r + h)) - 1) ≤
      Real.exp (Q * synchCharge P q h T) - 1 := by
  have hmulQ : Q * detIncrement P q r (T + h) =
      Q * detIncrement P q r (r + h) + Q * detIncrement P q (r + h) (T + h) := by
    rw [detIncrement_add P q r (r + h) (T + h)]
    ring
  have hspan := detIncrement_le_synchCharge_of_le hP hq hlj hfin hh hlow hr (by omega) hT
  have hspanQ := mul_le_mul_of_nonneg_left hspan hQ
  have hlate : 0 ≤ detIncrement P q (r + h) (T + h) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj (by omega)) (by omega)
      (hfin (r + h) (by omega) (by omega)) (hfin (T + h) (by omega) hT)
  have hlateQ : 0 ≤ Q * detIncrement P q (r + h) (T + h) := mul_nonneg hQ hlate
  have hsplit : Real.exp (Q * detIncrement P q (r + h) (T + h)) *
      (Real.exp (Q * detIncrement P q r (r + h)) - 1) =
      Real.exp (Q * detIncrement P q r (T + h)) -
        Real.exp (Q * detIncrement P q (r + h) (T + h)) := by
    rw [hmulQ, Real.exp_add, mul_sub, mul_one]
    ring
  have hupper : Real.exp (Q * detIncrement P q r (T + h)) ≤
      Real.exp (Q * synchCharge P q h T) := Real.exp_le_exp.mpr hspanQ
  have hone : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q (r + h) (T + h)) :=
    Real.one_le_exp hlateQ
  rw [hsplit]
  linarith only [hupper, hone]

/-- The `h` fresh terms of `V_{T+h}` are controlled by the powered recurrence at
their predecessors, which lie in the range of `V_T`. -/
theorem centered_service_new [NeZero d] [IsProbabilityMeasure P] {Q a Crec : ℝ}
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
    ∑ j ∈ Finset.Icc (T + 1) (T + h),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + h))) *
          centeredMoment P Q q j ^ Q ≤
      ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
            Real.exp (Q * synchCharge P q h T)) *
          ∑ j ∈ Finset.Icc (b + 1) T,
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
                Real.exp (Q * detIncrement P q j T)) *
              centeredMoment P Q q j ^ Q +
        ENNReal.ofReal ((h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
          (Real.exp (Q * synchCharge P q h T) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hlow : jStar ≤ T + 1 - h := by omega
  have hbeta0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q := by
    positivity
  have hc₂0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q := by positivity
  have hE0 : (0 : ℝ) ≤ Real.exp (Q * synchCharge P q h T) - 1 := by
    have hcharge0 := synchCharge_nonneg hP hq hlj hfin hh hlow hT
    have := Real.one_le_exp (mul_nonneg hQ0 hcharge0)
    linarith only [this]
  have hmap : (Finset.Icc (T + 1 - h) T).map (addRightEmbedding h) =
      Finset.Icc (T + 1) (T + h) := by
    rw [Finset.map_add_right_Icc]
    congr 1
    ring
  have hshift : ∀ f : ℤ → ℝ≥0∞,
      ∑ j ∈ Finset.Icc (T + 1) (T + h), f j = ∑ r ∈ Finset.Icc (T + 1 - h) T, f (r + h) := by
    intro f
    rw [← hmap, Finset.sum_map]
    simp [addRightEmbedding]
  have hterm : ∀ r ∈ Finset.Icc (T + 1 - h) T,
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - ((r + h : ℤ) : ℝ))) *
            Real.exp (Q * detIncrement P q (r + h) (T + h))) *
          centeredMoment P Q q (r + h) ^ Q ≤
        ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
              Real.exp (Q * synchCharge P q h T)) *
            (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                Real.exp (Q * detIncrement P q r T)) *
              centeredMoment P Q q r ^ Q) +
          ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
            (Real.exp (Q * synchCharge P q h T) - 1)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hrj : jStar ≤ r := by omega
    have hrec' := windowed_powered_recurrence hQ hCrec hP hunit hq hlj hfin hmom hrec hh hrj
      (by omega : r + h ≤ TMax)
    -- the weight of the fresh term
    have hw : (3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - ((r + h : ℤ) : ℝ))) =
        (3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) := by
      congr 1
      push_cast
      ring
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) := Real.rpow_nonneg (by norm_num) _
    have hwle : (3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hTr : (0 : ℝ) ≤ (T : ℝ) - (r : ℝ) := by
        have : (r : ℤ) ≤ T := hr.2
        have hcast : ((r : ℤ) : ℝ) ≤ ((T : ℤ) : ℝ) := by exact_mod_cast this
        linarith only [hcast]
      nlinarith only [hTr, ha]
    have hlate0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q (r + h) (T + h)) := (Real.exp_pos _).le
    have hW0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
        Real.exp (Q * detIncrement P q (r + h) (T + h)) := mul_nonneg hw0 hlate0
    -- multiply the powered recurrence by the terminal weight
    have hstep := mul_le_mul' (le_refl (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
      Real.exp (Q * detIncrement P q (r + h) (T + h))))) hrec'
    rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hW0, ← ENNReal.ofReal_mul hW0] at hstep
    rw [hw]
    refine le_trans hstep (add_le_add ?_ ?_)
    · -- the principal part
      have hmulQ : Q * detIncrement P q r (T + h) =
          Q * detIncrement P q r (r + h) + Q * detIncrement P q (r + h) (T + h) := by
        rw [detIncrement_add P q r (r + h) (T + h)]
        ring
      have hmulQ' : Q * detIncrement P q r (T + h) =
          Q * detIncrement P q r T + Q * detIncrement P q T (T + h) := by
        rw [detIncrement_add P q r T (T + h)]
        ring
      have hcharge := detIncrement_le_synchCharge_step hP hq hlj hfin hh hlow hT
      have hchargeQ := mul_le_mul_of_nonneg_left hcharge hQ0
      have hexp : Real.exp (Q * detIncrement P q r (r + h)) *
          Real.exp (Q * detIncrement P q (r + h) (T + h)) ≤
          Real.exp (Q * synchCharge P q h T) * Real.exp (Q * detIncrement P q r T) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith only [hmulQ, hmulQ', hchargeQ])
      have hbetaE0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q *
          ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q * Real.exp (Q * synchCharge P q h T) :=
        mul_nonneg hbeta0 (Real.exp_pos _).le
      have hcoefle : (3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
            Real.exp (Q * detIncrement P q (r + h) (T + h)) *
          (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
            Real.exp (Q * detIncrement P q r (r + h))) ≤
          2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
              Real.exp (Q * synchCharge P q h T) *
            ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) * Real.exp (Q * detIncrement P q r T)) := by
        calc (3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                Real.exp (Q * detIncrement P q (r + h) (T + h)) *
              (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                Real.exp (Q * detIncrement P q r (r + h)))
            = 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                  (Real.exp (Q * detIncrement P q r (r + h)) *
                    Real.exp (Q * detIncrement P q (r + h) (T + h)))) := by ring
          _ ≤ 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                  (Real.exp (Q * synchCharge P q h T) *
                    Real.exp (Q * detIncrement P q r T))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hw0) hbeta0
          _ = 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                Real.exp (Q * synchCharge P q h T) *
              ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                Real.exp (Q * detIncrement P q r T)) := by ring
      refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoefle) le_rfl) ?_
      rw [ENNReal.ofReal_mul hbetaE0, mul_assoc]
    · -- the fresh error
      refine ENNReal.ofReal_le_ofReal ?_
      have hfresh := exp_mul_exp_sub_one_le hQ0 hP hq hlj hfin hh hlow hr.1 hr.2 hT
      have hgain0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q r (r + h)) - 1 := by
        have hnn : 0 ≤ detIncrement P q r (r + h) :=
          Recurrence.detIncrement_nonneg hP hq (le_trans hlj hrj) (by omega)
            (hfin r hrj (by omega)) (hfin (r + h) (by omega) (by omega))
        have := Real.one_le_exp (mul_nonneg hQ0 hnn)
        linarith only [this]
      calc (3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
              Real.exp (Q * detIncrement P q (r + h) (T + h)) *
            (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              (Real.exp (Q * detIncrement P q r (r + h)) - 1))
          = 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                (Real.exp (Q * detIncrement P q (r + h) (T + h)) *
                  (Real.exp (Q * detIncrement P q r (r + h)) - 1))) := by ring
        _ ≤ 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              (Real.exp (Q * synchCharge P q h T) - 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hc₂0
            have hinner : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q (r + h) (T + h)) *
                (Real.exp (Q * detIncrement P q r (r + h)) - 1) :=
              mul_nonneg hlate0 hgain0
            nlinarith only [hwle, hw0, hinner, hfresh]
  have hcard : (Finset.Icc (T + 1 - h) T).card = h.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_trans zero_le_one hh)
  have hsubset : Finset.Icc (T + 1 - h) T ⊆ Finset.Icc (b + 1) T := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  rw [hshift]
  calc ∑ r ∈ Finset.Icc (T + 1 - h) T,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + h : ℤ) : ℝ) - ((r + h : ℤ) : ℝ))) *
            Real.exp (Q * detIncrement P q (r + h) (T + h))) *
          centeredMoment P Q q (r + h) ^ Q
      ≤ ∑ r ∈ Finset.Icc (T + 1 - h) T,
          (ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                Real.exp (Q * synchCharge P q h T)) *
              (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                  Real.exp (Q * detIncrement P q r T)) *
                centeredMoment P Q q r ^ Q) +
            ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              (Real.exp (Q * synchCharge P q h T) - 1))) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
              Real.exp (Q * synchCharge P q h T)) *
            (∑ r ∈ Finset.Icc (T + 1 - h) T,
              ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
                  Real.exp (Q * detIncrement P q r T)) *
                centeredMoment P Q q r ^ Q) +
          (Finset.Icc (T + 1 - h) T).card •
            ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              (Real.exp (Q * synchCharge P q h T) - 1)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const]
    _ ≤ ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
              Real.exp (Q * synchCharge P q h T)) *
            (∑ j ∈ Finset.Icc (b + 1) T,
              ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
                  Real.exp (Q * detIncrement P q j T)) *
                centeredMoment P Q q j ^ Q) +
          ENNReal.ofReal ((h : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
            (Real.exp (Q * synchCharge P q h T) - 1)) := by
        refine add_le_add (mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hsubset)) ?_
        rw [hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast, hcast,
          ← ENNReal.ofReal_mul (le_trans zero_le_one (by exact_mod_cast hh))]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        ring

end Window

end

end PortableHistory
end HighContrast
end Homogenization
