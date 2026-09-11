/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.CheckpointMoment
import HCPoly.Provider.PortableHistory.WindowedRecurrence

/-!
# The rows of `e.fixed.geometry.profile.startup`

Write `D = Δ_{b,b+L}^q`.  The inherited row of `e.scale.selection.complete.profile`
at `b+L` is bounded by `e^{QD}𝓗_q(b)`, and each of the `L` new nonlinear terms by
`e^{QΔ_{j,b+L}^q} - 1 ≤ e^{QD} - 1`.  Each of the `L` new centered scales `b+m`
is reached by the recurrence applied directly from `b` with service length `m`,
raised to the power `Q` and transported to `b+L`, which is the startup bound
for the new fluctuation terms.  The unit-size absorption
`e^{QD}X ≤ X + (e^{QD} - 1)` for `X ≤ 1`, recorded first, is what keeps every
exponential factor from leaving a scale-independent positive error.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The unit-size absorption.**  If `X ≤ 1` then `EX ≤ X + (E - 1)` when
`E ≥ 1`. -/
theorem ofReal_mul_le_add_of_le_one {E : ℝ} (hE : 1 ≤ E) {X : ℝ≥0∞} (hX : X ≤ 1) :
    ENNReal.ofReal E * X ≤ X + ENNReal.ofReal (E - 1) := by
  have hsplit : ENNReal.ofReal E = 1 + ENNReal.ofReal (E - 1) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith only [hE])]
    congr 1
    ring
  rw [hsplit, add_mul, one_mul]
  exact add_le_add le_rfl (le_trans (mul_le_mul' le_rfl hX) (le_of_eq (mul_one _)))

/-- Two real coefficients in front of one extended nonnegative quantity merge. -/
theorem ofReal_mul_ofReal_mul {A : ℝ} (hA : 0 ≤ A) (B : ℝ) (X : ℝ≥0∞) :
    ENNReal.ofReal A * (ENNReal.ofReal B * X) = ENNReal.ofReal (A * B) * X := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hA]

section Window

variable {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-! ## The three rows at the checkpoint -/

/-- The inherited row at the checkpoint carries `e^{QD}`. -/
theorem startup_inherited [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ} (hQ : 0 ≤ Q)
    (ha : 0 < a)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b L : ℤ} (hL : 1 ≤ L) (hb : jStar ≤ b) (hbL : b + L ≤ TMax) :
    ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b (b + L)))) *
        portableHistory P Q a rhoMax q jStar b ≤
      ENNReal.ofReal (Real.exp (Q * detIncrement P q b (b + L))) *
        portableHistory P Q a rhoMax q jStar b := by
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hgain := one_add_frakH_le_exp hQ hP hq hlj hfin (s := b) (t := b + L) hb (by omega) hbL
  have hgain0 : (0 : ℝ) ≤ 1 + frakH Q (relMean P q b (b + L)) := by
    have := frakH_relMean_nonneg hQ hP hq hlj hfin (j := b) (T := b + L) hb (by omega) hbL
    linarith only [this]
  have hwle : (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (b : ℝ))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hcast : ((b + L : ℤ) : ℝ) - (b : ℝ) = (L : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith only [hLr, ha]
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (b : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  nlinarith only [hwle, hw0, hgain, hgain0]

/-- Each new nonlinear term at the checkpoint is at most `e^{QD} - 1`. -/
theorem startup_nonlinear [NeZero d] [IsProbabilityMeasure P] {Q a : ℝ} (hQ : 0 ≤ Q)
    (ha : 0 < a)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b L : ℤ} (hL : 1 ≤ L) (hb : jStar ≤ b) (hbL : b + L ≤ TMax) :
    ∑ j ∈ Finset.Ico b (b + L),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (b + L))) ≤
      ENNReal.ofReal ((L : ℝ) * (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
  have hD0 : 0 ≤ detIncrement P q b (b + L) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj hb) (by omega) (hfin b hb (by omega))
      (hfin (b + L) (by omega) hbL)
  have hE1 : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q b (b + L)) :=
    Real.one_le_exp (mul_nonneg hQ hD0)
  have hterm : ∀ j ∈ Finset.Ico b (b + L),
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (b + L))) ≤
        ENNReal.ofReal (Real.exp (Q * detIncrement P q b (b + L)) - 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    refine ENNReal.ofReal_le_ofReal ?_
    have hgain := one_add_frakH_le_exp hQ hP hq hlj hfin (s := j) (t := b + L)
      (by omega) (by omega) hbL
    have hgain0 := frakH_relMean_nonneg hQ hP hq hlj hfin (j := j) (T := b + L)
      (by omega) (by omega) hbL
    have hsplit : Q * detIncrement P q b (b + L) =
        Q * detIncrement P q b j + Q * detIncrement P q j (b + L) := by
      rw [detIncrement_add P q b j (b + L)]
      ring
    have hearly : 0 ≤ detIncrement P q b j :=
      Recurrence.detIncrement_nonneg hP hq (le_trans hlj hb) (by omega) (hfin b hb (by omega))
        (hfin j (by omega) (by omega))
    have hmono : Real.exp (Q * detIncrement P q j (b + L)) ≤
        Real.exp (Q * detIncrement P q b (b + L)) :=
      Real.exp_le_exp.mpr (by nlinarith only [hsplit, hearly, hQ])
    have hwle : (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - 1 - (j : ℝ))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hjr : (j : ℝ) ≤ ((b + L : ℤ) : ℝ) - 1 := by
        have hji : (j : ℤ) ≤ (b + L : ℤ) - 1 := by omega
        have hcast : ((j : ℤ) : ℝ) ≤ (((b + L : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hji
        push_cast at hcast ⊢
        linarith only [hcast]
      nlinarith only [hjr, ha]
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - 1 - (j : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    nlinarith only [hwle, hw0, hgain, hgain0, hmono]
  have hcard : (Finset.Ico b (b + L)).card = L.toNat := by
    rw [Int.card_Ico]
    congr 1
    ring
  have hcast : ((L.toNat : ℕ) : ℝ) = (L : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_trans zero_le_one hL)
  calc ∑ j ∈ Finset.Ico b (b + L),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j (b + L)))
      ≤ ∑ _j ∈ Finset.Ico b (b + L),
          ENNReal.ofReal (Real.exp (Q * detIncrement P q b (b + L)) - 1) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((L : ℝ) * (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast, hcast,
          ← ENNReal.ofReal_mul (le_trans zero_le_one (by exact_mod_cast hL))]

/-! ## The new centered scales at the checkpoint -/

/-- **The startup bound for the new fluctuation terms, summed over the `L` new
centered scales.** -/
theorem startup_centered [NeZero d] [IsProbabilityMeasure P] {Q a Crec : ℝ}
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
    {b L : ℤ} (hL : 1 ≤ L) (hb : jStar ≤ b) (hbL : b + L ≤ TMax) :
    ∑ j ∈ Finset.Icc (b + 1) (b + L),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (b + L))) *
          centeredMoment P Q q j ^ Q ≤
      ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q) *
            Real.exp (Q * detIncrement P q b (b + L))) *
          centeredMoment P Q q b ^ Q +
        ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
          (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans zero_le_one hL
  have hbeta0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q := by positivity
  have hD0 : 0 ≤ detIncrement P q b (b + L) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj hb) (by omega) (hfin b hb (by omega))
      (hfin (b + L) (by omega) hbL)
  have hE1 : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q b (b + L)) :=
    Real.one_le_exp (mul_nonneg hQ0 hD0)
  have hterm : ∀ j ∈ Finset.Icc (b + 1) (b + L),
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (b + L))) *
          centeredMoment P Q q j ^ Q ≤
        ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q *
              Real.exp (Q * detIncrement P q b (b + L))) *
            centeredMoment P Q q b ^ Q +
          ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
            (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjeq : b + (j - b) = j := by ring
    have hstep0 := windowed_powered_recurrence hQ hCrec hP hunit hq hlj hfin hmom hrec
      (by omega : (1 : ℤ) ≤ j - b) hb (by omega : b + (j - b) ≤ TMax)
    rw [hjeq] at hstep0
    -- the terminal weight
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hwle : (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hjr : (j : ℝ) ≤ ((b + L : ℤ) : ℝ) := by exact_mod_cast hj.2
      nlinarith only [hjr, ha]
    have hlate0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q j (b + L)) := (Real.exp_pos _).le
    have hW0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
        Real.exp (Q * detIncrement P q j (b + L)) := mul_nonneg hw0 hlate0
    have hstep := mul_le_mul' (le_refl (ENNReal.ofReal
      ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
        Real.exp (Q * detIncrement P q j (b + L))))) hstep0
    rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hW0, ← ENNReal.ofReal_mul hW0] at hstep
    refine le_trans hstep (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      (ENNReal.ofReal_le_ofReal ?_))
    · -- the principal part
      have hsplit : Q * detIncrement P q b (b + L) =
          Q * detIncrement P q b j + Q * detIncrement P q j (b + L) := by
        rw [detIncrement_add P q b j (b + L)]
        ring
      have hexp : Real.exp (Q * detIncrement P q b j) *
          Real.exp (Q * detIncrement P q j (b + L)) =
          Real.exp (Q * detIncrement P q b (b + L)) := by
        rw [← Real.exp_add, hsplit]
      have hgeom : ((3 : ℝ) ^ (-((j - b : ℤ) : ℝ) * (d : ℝ) / 2)) ^ Q ≤ 1 := by
        refine Real.rpow_le_one (Real.rpow_nonneg (by norm_num) _) ?_ hQ0
        refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
        have hjb : (1 : ℝ) ≤ ((j - b : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ j - b)
        have hdr : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        nlinarith only [hjb, hdr]
      have hgeom0 : (0 : ℝ) ≤ ((3 : ℝ) ^ (-((j - b : ℤ) : ℝ) * (d : ℝ) / 2)) ^ Q :=
        Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) _
      calc (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
              Real.exp (Q * detIncrement P q j (b + L)) *
            (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-((j - b : ℤ) : ℝ) * (d : ℝ) / 2)) ^ Q *
              Real.exp (Q * detIncrement P q b j))
          = (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
              (((3 : ℝ) ^ (-((j - b : ℤ) : ℝ) * (d : ℝ) / 2)) ^ Q *
                (2 ^ (Q - 1) * Crec ^ Q *
                  (Real.exp (Q * detIncrement P q b j) *
                    Real.exp (Q * detIncrement P q j (b + L))))) := by ring
        _ = (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
              (((3 : ℝ) ^ (-((j - b : ℤ) : ℝ) * (d : ℝ) / 2)) ^ Q *
                (2 ^ (Q - 1) * Crec ^ Q * Real.exp (Q * detIncrement P q b (b + L)))) := by
            rw [hexp]
        _ ≤ 2 ^ (Q - 1) * Crec ^ Q * Real.exp (Q * detIncrement P q b (b + L)) := by
            have hpos : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q *
                Real.exp (Q * detIncrement P q b (b + L)) :=
              mul_nonneg hbeta0 (Real.exp_pos _).le
            have hinner : ((3 : ℝ) ^ (-((j - b : ℤ) : ℝ) * (d : ℝ) / 2)) ^ Q *
                (2 ^ (Q - 1) * Crec ^ Q * Real.exp (Q * detIncrement P q b (b + L))) ≤
                2 ^ (Q - 1) * Crec ^ Q * Real.exp (Q * detIncrement P q b (b + L)) := by
              nlinarith only [hgeom, hpos]
            have hinner0 : (0 : ℝ) ≤ ((3 : ℝ) ^ (-((j - b : ℤ) : ℝ) * (d : ℝ) / 2)) ^ Q *
                (2 ^ (Q - 1) * Crec ^ Q * Real.exp (Q * detIncrement P q b (b + L))) :=
              mul_nonneg hgeom0 hpos
            nlinarith only [hwle, hinner, hinner0]
    · -- the fresh error
      have hearly0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q b j) - 1 := by
        have hbj : 0 ≤ detIncrement P q b j :=
          Recurrence.detIncrement_nonneg hP hq (le_trans hlj hb) (by omega) (hfin b hb (by omega))
            (hfin j (by omega) (by omega))
        have := Real.one_le_exp (mul_nonneg hQ0 hbj)
        linarith only [this]
      have hlate1 : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q j (b + L)) := by
        have hjL : 0 ≤ detIncrement P q j (b + L) :=
          Recurrence.detIncrement_nonneg hP hq (le_trans hlj (by omega)) (by omega)
            (hfin j (by omega) (by omega)) (hfin (b + L) (by omega) hbL)
        exact Real.one_le_exp (mul_nonneg hQ0 hjL)
      have hsplit : Q * detIncrement P q b (b + L) =
          Q * detIncrement P q b j + Q * detIncrement P q j (b + L) := by
        rw [detIncrement_add P q b j (b + L)]
        ring
      have hprod : Real.exp (Q * detIncrement P q j (b + L)) *
          (Real.exp (Q * detIncrement P q b j) - 1) ≤
          Real.exp (Q * detIncrement P q b (b + L)) - 1 := by
        have heq : Real.exp (Q * detIncrement P q j (b + L)) *
            (Real.exp (Q * detIncrement P q b j) - 1) =
            Real.exp (Q * detIncrement P q b (b + L)) -
              Real.exp (Q * detIncrement P q j (b + L)) := by
          rw [mul_sub, mul_one, ← Real.exp_add, hsplit]
          ring_nf
        rw [heq]
        linarith only [hlate1]
      have hprod0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q j (b + L)) *
          (Real.exp (Q * detIncrement P q b j) - 1) := mul_nonneg hlate0 hearly0
      have hc₂0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q := by positivity
      calc (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
              Real.exp (Q * detIncrement P q j (b + L)) *
            (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q * (Real.exp (Q * detIncrement P q b j) - 1))
          = 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
                (Real.exp (Q * detIncrement P q j (b + L)) *
                  (Real.exp (Q * detIncrement P q b j) - 1))) := by ring
        _ ≤ 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              (Real.exp (Q * detIncrement P q b (b + L)) - 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hc₂0
            nlinarith only [hwle, hw0, hprod, hprod0]
  have hcard : (Finset.Icc (b + 1) (b + L)).card = L.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hcast : ((L.toNat : ℕ) : ℝ) = (L : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_trans zero_le_one hL)
  have hcoef1 : (L.toNat : ℝ≥0∞) *
      (ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * Real.exp (Q * detIncrement P q b (b + L))) *
        centeredMoment P Q q b ^ Q) =
      ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q) *
          Real.exp (Q * detIncrement P q b (b + L))) *
        centeredMoment P Q q b ^ Q := by
    rw [← ENNReal.ofReal_natCast, hcast, ofReal_mul_ofReal_mul hL0]
    congr 2
    ring
  have hcoef2 : (L.toNat : ℝ≥0∞) *
      ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
        (Real.exp (Q * detIncrement P q b (b + L)) - 1)) =
      ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
        (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
    rw [← ENNReal.ofReal_natCast, hcast, ← ENNReal.ofReal_mul hL0]
    congr 1
    ring
  calc ∑ j ∈ Finset.Icc (b + 1) (b + L),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (b + L))) *
          centeredMoment P Q q j ^ Q
      ≤ ∑ _j ∈ Finset.Icc (b + 1) (b + L),
          (ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q *
                Real.exp (Q * detIncrement P q b (b + L))) *
              centeredMoment P Q q b ^ Q +
            ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
              (Real.exp (Q * detIncrement P q b (b + L)) - 1))) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q) *
            Real.exp (Q * detIncrement P q b (b + L))) *
          centeredMoment P Q q b ^ Q +
        ENNReal.ofReal ((L : ℝ) * (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q) *
          (Real.exp (Q * detIncrement P q b (b + L)) - 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, hcard,
          nsmul_eq_mul, nsmul_eq_mul, hcoef1, hcoef2]

end Window

end

end PortableHistory
end HighContrast
end Homogenization
