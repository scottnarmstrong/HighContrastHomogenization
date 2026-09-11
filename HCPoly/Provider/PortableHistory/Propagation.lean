/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.LeftRows
import HCPoly.Provider.PortableHistory.WindowedRecurrence

/-!
# The new centered scales of the propagation estimate

The propagation estimate of `p.fixed.geometry.one.grid.propagation` reaches the scales
`T < s ≤ T+L` by the induction bounding the new fluctuation terms: with

`Y_s = e^{QΔ_{s,T+L}^q}(v_s^q)^Q`,   `D = Δ_{T,T+L}^q`,

the powered recurrence at the predecessor `s-h` gives
`Y_s ≤ β_h Y_{s-h} + C(d,Q)(e^{QΔ_{s-h,T+L}^q} - 1)`.  The predecessors reach back to `T+1-h`; below `T` the two left rows of a
unit-size profile start the induction, and the determinant term is controlled by
`(e^{QD} - 1)` together with `𝒫_q(T;b)` in either case — through
`e^{QΔ_{s-h,T+L}^q} - 1 = e^{QΔ_{s-h,T}^q}(e^{QD} - 1) + (e^{QΔ_{s-h,T}^q} - 1)`
when `s-h ≤ T`, and directly when `s-h > T`.

The induction is stated against an abstract constant `K` subject to the two
inequalities it has to satisfy, one for the start and one for the step.
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

/-- **The induction bounding the new fluctuation terms.**  Every scale of
`[T+1-h, T+L]` carries a transported powered moment bounded by
`K(𝒫_q(T;b) + (e^{QD} - 1))`. -/
theorem transported_moment_le [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax Crec K : ℝ}
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
    {b h L T s : ℤ} (hh : 1 ≤ h) (hL : 1 ≤ L) (hb : jStar ≤ b) (hbT : b + h ≤ T)
    (hTL : T + L ≤ TMax)
    (hKbase : (3 : ℝ) ^ (a * (h : ℝ)) ≤ K)
    (hKstep : 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q * K +
        2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
          (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
            (3 : ℝ) ^ (a * (h : ℝ))) ≤ K)
    (hprof : portableProfile P Q a rhoMax q jStar b T ≤ 1)
    (hs : T + 1 - h ≤ s) (hsT : s ≤ T + L) :
    ENNReal.ofReal (Real.exp (Q * detIncrement P q s (T + L))) * centeredMoment P Q q s ^ Q ≤
      ENNReal.ofReal K *
        (portableProfile P Q a rhoMax q jStar b T +
          ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hK0 : (0 : ℝ) ≤ K := le_trans (Real.rpow_nonneg (by norm_num) _) hKbase
  have hbeta0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q := by
    positivity
  have hc0 : (0 : ℝ) ≤ 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q := by positivity
  have hCld0 : (0 : ℝ) ≤ Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
      (3 : ℝ) ^ (a * (h : ℝ)) := by positivity
  have h1Cld0 : (0 : ℝ) ≤ 1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
      (3 : ℝ) ^ (a * (h : ℝ)) := by linarith only [hCld0]
  have hD0 : 0 ≤ detIncrement P q T (T + L) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj (by omega)) (by omega)
      (hfin T (by omega) (by omega)) (hfin (T + L) (by omega) hTL)
  have hED1 : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q T (T + L)) :=
    Real.one_le_exp (mul_nonneg hQ0 hD0)
  have hED0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q T (T + L)) - 1 := by
    linarith only [hED1]
  have hmain : ∀ n : ℕ, ∀ r : ℤ, r = T + 1 - h + (n : ℤ) → r ≤ T + L →
      ENNReal.ofReal (Real.exp (Q * detIncrement P q r (T + L))) *
          centeredMoment P Q q r ^ Q ≤
        ENNReal.ofReal K *
          (portableProfile P Q a rhoMax q jStar b T +
            ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro r hrdef hrle
      have hrlow : T + 1 - h ≤ r := by omega
      rcases le_or_gt r T with hbaseCase | hstepCase
      · -- the left scales
        have hsplit : Q * detIncrement P q r (T + L) =
            Q * detIncrement P q r T + Q * detIncrement P q T (T + L) := by
          rw [detIncrement_add P q r T (T + L)]
          ring
        have hfac : Real.exp (Q * detIncrement P q r (T + L)) =
            Real.exp (Q * detIncrement P q T (T + L)) *
              Real.exp (Q * detIncrement P q r T) := by
          rw [← Real.exp_add, hsplit]
          ring_nf
        calc ENNReal.ofReal (Real.exp (Q * detIncrement P q r (T + L))) *
              centeredMoment P Q q r ^ Q
            = ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
                (ENNReal.ofReal (Real.exp (Q * detIncrement P q r T)) *
                  centeredMoment P Q q r ^ Q) := by
              rw [ofReal_mul_ofReal_mul (Real.exp_pos _).le, ← hfac]
          _ ≤ ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
                (ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
                  portableProfile P Q a rhoMax q jStar b T) :=
              mul_le_mul' le_rfl (exp_mul_centeredMoment_le ha hbT hrlow hbaseCase)
          _ = ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
                (ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
                  portableProfile P Q a rhoMax q jStar b T) := by
              rw [ofReal_mul_ofReal_mul (Real.exp_pos _).le,
                ofReal_mul_ofReal_mul (Real.rpow_nonneg (by norm_num) _),
                mul_comm (Real.exp (Q * detIncrement P q T (T + L)))
                  ((3 : ℝ) ^ (a * (h : ℝ)))]
          _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
                (portableProfile P Q a rhoMax q jStar b T +
                  ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) :=
              mul_le_mul' le_rfl (ofReal_mul_le_add_of_le_one hED1 hprof)
          _ ≤ ENNReal.ofReal K *
                (portableProfile P Q a rhoMax q jStar b T +
                  ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hKbase) le_rfl
      · -- the new scales
        have hpred : T + 1 - h ≤ r - h := by omega
        have hpredjs : jStar ≤ r - h := by omega
        have hreq : r - h + h = r := by ring
        have hstep0 := windowed_powered_recurrence hQ hCrec hP hunit hq hlj hfin hmom hrec hh
          hpredjs (by omega : r - h + h ≤ TMax)
        rw [hreq] at hstep0
        have hW0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q r (T + L)) := (Real.exp_pos _).le
        have hmul := mul_le_mul' (le_refl (ENNReal.ofReal
          (Real.exp (Q * detIncrement P q r (T + L))))) hstep0
        rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hW0, ← ENNReal.ofReal_mul hW0] at hmul
        have hadd : Q * detIncrement P q (r - h) (T + L) =
            Q * detIncrement P q (r - h) r + Q * detIncrement P q r (T + L) := by
          rw [detIncrement_add P q (r - h) r (T + L)]
          ring
        have hrTL0 : 0 ≤ detIncrement P q r (T + L) :=
          Recurrence.detIncrement_nonneg hP hq (le_trans hlj (by omega)) (by omega)
            (hfin r (by omega) (by omega)) (hfin (T + L) (by omega) hTL)
        have hrone : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q r (T + L)) :=
          Real.one_le_exp (mul_nonneg hQ0 hrTL0)
        -- the determinant term at the predecessor
        have hEexcess : ENNReal.ofReal (Real.exp (Q * detIncrement P q (r - h) (T + L)) - 1) ≤
            ENNReal.ofReal (1 + Q *
                Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                (3 : ℝ) ^ (a * (h : ℝ))) *
              (portableProfile P Q a rhoMax q jStar b T +
                ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
          rcases le_or_gt (r - h) T with hle | hgt
          · have hsplit : Q * detIncrement P q (r - h) (T + L) =
                Q * detIncrement P q (r - h) T + Q * detIncrement P q T (T + L) := by
              rw [detIncrement_add P q (r - h) T (T + L)]
              ring
            have hdec : Real.exp (Q * detIncrement P q (r - h) (T + L)) - 1 =
                Real.exp (Q * detIncrement P q (r - h) T) *
                    (Real.exp (Q * detIncrement P q T (T + L)) - 1) +
                  (Real.exp (Q * detIncrement P q (r - h) T) - 1) := by
              rw [hsplit, Real.exp_add]
              ring
            have hld : ENNReal.ofReal (Real.exp (Q * detIncrement P q (r - h) T) - 1) ≤
                ENNReal.ofReal (Q *
                    Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ))) *
                  portableProfile P Q a rhoMax q jStar b T :=
              exp_detIncrement_sub_one_le hQ ha hP hq hlj hfin hb hbT (by omega) hpred hle hprof
            have hldr : Real.exp (Q * detIncrement P q (r - h) T) - 1 ≤
                Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                  (3 : ℝ) ^ (a * (h : ℝ)) := by
              refine (ENNReal.ofReal_le_ofReal_iff hCld0).mp (le_trans hld ?_)
              calc ENNReal.ofReal (Q *
                      Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                      (3 : ℝ) ^ (a * (h : ℝ))) *
                    portableProfile P Q a rhoMax q jStar b T
                  ≤ ENNReal.ofReal (Q *
                      Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                      (3 : ℝ) ^ (a * (h : ℝ))) * 1 := mul_le_mul' le_rfl hprof
                _ = _ := mul_one _
            have hnn1 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q (r - h) T) *
                (Real.exp (Q * detIncrement P q T (T + L)) - 1) :=
              mul_nonneg (Real.exp_pos _).le hED0
            have hnn2 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q (r - h) T) - 1 := by
              have hpd : 0 ≤ detIncrement P q (r - h) T :=
                Recurrence.detIncrement_nonneg hP hq (le_trans hlj hpredjs) hle
                  (hfin (r - h) hpredjs (by omega)) (hfin T (by omega) (by omega))
              have := Real.one_le_exp (mul_nonneg hQ0 hpd)
              linarith only [this]
            have hA : ENNReal.ofReal (Real.exp (Q * detIncrement P q (r - h) T) *
                (Real.exp (Q * detIncrement P q T (T + L)) - 1)) ≤
                ENNReal.ofReal ((1 + Q *
                    Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ))) *
                  (Real.exp (Q * detIncrement P q T (T + L)) - 1)) :=
              ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (by linarith only [hldr]) hED0)
            rw [hdec, ENNReal.ofReal_add hnn1 hnn2]
            refine le_trans (add_le_add hA hld) ?_
            calc ENNReal.ofReal ((1 + Q *
                    Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ))) *
                  (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
                ENNReal.ofReal (Q *
                    Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ))) *
                  portableProfile P Q a rhoMax q jStar b T
                ≤ ENNReal.ofReal (1 + Q *
                      Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                      (3 : ℝ) ^ (a * (h : ℝ))) *
                    ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1) +
                  ENNReal.ofReal (1 + Q *
                      Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                      (3 : ℝ) ^ (a * (h : ℝ))) *
                    portableProfile P Q a rhoMax q jStar b T :=
                  add_le_add (le_of_eq (ENNReal.ofReal_mul h1Cld0))
                    (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith only [hCld0])) le_rfl)
              _ = _ := by ring
          · have hmono : detIncrement P q (r - h) (T + L) ≤ detIncrement P q T (T + L) := by
              have hsp := detIncrement_add P q T (r - h) (T + L)
              have hnn : 0 ≤ detIncrement P q T (r - h) :=
                Recurrence.detIncrement_nonneg hP hq (le_trans hlj (by omega)) (by omega)
                  (hfin T (by omega) (by omega)) (hfin (r - h) hpredjs (by omega))
              linarith only [hsp, hnn]
            have hexp : Real.exp (Q * detIncrement P q (r - h) (T + L)) - 1 ≤
                Real.exp (Q * detIncrement P q T (T + L)) - 1 := by
              have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmono hQ0)
              linarith only [this]
            calc ENNReal.ofReal (Real.exp (Q * detIncrement P q (r - h) (T + L)) - 1)
                ≤ ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1) :=
                  ENNReal.ofReal_le_ofReal hexp
              _ ≤ portableProfile P Q a rhoMax q jStar b T +
                    ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1) :=
                  self_le_add_left _ _
              _ ≤ ENNReal.ofReal (1 + Q *
                      Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                      (3 : ℝ) ^ (a * (h : ℝ))) *
                    (portableProfile P Q a rhoMax q jStar b T +
                      ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
                  refine le_trans (le_of_eq (one_mul _).symm) (mul_le_mul' ?_ le_rfl)
                  rw [← ENNReal.ofReal_one]
                  exact ENNReal.ofReal_le_ofReal (by linarith only [hCld0])
        -- the two pieces
        have hfirst : ENNReal.ofReal (Real.exp (Q * detIncrement P q r (T + L)) *
              (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                Real.exp (Q * detIncrement P q (r - h) r))) *
            centeredMoment P Q q (r - h) ^ Q ≤
            ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q *
                ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q) *
              (ENNReal.ofReal K *
                (portableProfile P Q a rhoMax q jStar b T +
                  ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1))) := by
          have hprin : Real.exp (Q * detIncrement P q r (T + L)) *
              (2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                Real.exp (Q * detIncrement P q (r - h) r)) =
              2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q *
                Real.exp (Q * detIncrement P q (r - h) (T + L)) := by
            rw [hadd, Real.exp_add]
            ring
          rw [hprin, ← ofReal_mul_ofReal_mul hbeta0]
          refine mul_le_mul' le_rfl (ih (n - h.toNat) (by omega) (r - h) (by omega) (by omega))
        have hsecond : ENNReal.ofReal (Real.exp (Q * detIncrement P q r (T + L)) *
              (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                (Real.exp (Q * detIncrement P q (r - h) r) - 1))) ≤
            ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                  (3 : ℝ) ^ (a * (h : ℝ)))) *
              (portableProfile P Q a rhoMax q jStar b T +
                ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
          have heq : Real.exp (Q * detIncrement P q r (T + L)) *
              (Real.exp (Q * detIncrement P q (r - h) r) - 1) =
              Real.exp (Q * detIncrement P q (r - h) (T + L)) -
                Real.exp (Q * detIncrement P q r (T + L)) := by
            rw [mul_sub, mul_one, ← Real.exp_add, hadd]
            ring_nf
          have herr : Real.exp (Q * detIncrement P q r (T + L)) *
              (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                (Real.exp (Q * detIncrement P q (r - h) r) - 1)) ≤
              2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                (Real.exp (Q * detIncrement P q (r - h) (T + L)) - 1) := by
            calc Real.exp (Q * detIncrement P q r (T + L)) *
                  (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                    (Real.exp (Q * detIncrement P q (r - h) r) - 1))
                = 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                    (Real.exp (Q * detIncrement P q r (T + L)) *
                      (Real.exp (Q * detIncrement P q (r - h) r) - 1)) := by ring
              _ = 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                    (Real.exp (Q * detIncrement P q (r - h) (T + L)) -
                      Real.exp (Q * detIncrement P q r (T + L))) := by rw [heq]
              _ ≤ 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                    (Real.exp (Q * detIncrement P q (r - h) (T + L)) - 1) :=
                  mul_le_mul_of_nonneg_left (by linarith only [hrone]) hc0
          refine le_trans (ENNReal.ofReal_le_ofReal herr) ?_
          rw [ENNReal.ofReal_mul hc0]
          exact le_trans (mul_le_mul' le_rfl hEexcess)
            (le_of_eq (ofReal_mul_ofReal_mul hc0 _ _))
        refine le_trans hmul (le_trans (add_le_add hfirst hsecond) ?_)
        calc ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q *
                ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q) *
              (ENNReal.ofReal K *
                (portableProfile P Q a rhoMax q jStar b T +
                  ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1))) +
              ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                  (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ)))) *
                (portableProfile P Q a rhoMax q jStar b T +
                  ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1))
            = ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q *
                  ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q * K +
                2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
                  (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ)))) *
                (portableProfile P Q a rhoMax q jStar b T +
                  ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
              rw [ofReal_mul_ofReal_mul hbeta0, ← add_mul,
                ← ENNReal.ofReal_add (mul_nonneg hbeta0 hK0) (mul_nonneg hc0 h1Cld0)]
          _ ≤ ENNReal.ofReal K *
                (portableProfile P Q a rhoMax q jStar b T +
                  ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hKstep) le_rfl
  exact hmain (s - (T + 1 - h)).toNat s (by omega) hsT

end Window

end

end PortableHistory
end HighContrast
end Homogenization
