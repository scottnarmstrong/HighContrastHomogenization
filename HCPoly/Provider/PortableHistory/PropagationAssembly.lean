/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.PropagationRows
import HCPoly.Provider.PortableHistory.Startup

/-!
# The propagation estimate

`e.fixed.geometry.profile.fixed.span` propagates a unit-size profile over a
bounded number of scales:

`𝒫_q(T+L;b) ≤ C_L𝒫_q(T;b) + C_L(e^{QD} - 1)`   when `𝒫_q(T;b) ≤ 1`,

with `D = Δ_{T,T+L}^q`.  The three old rows are transported at the cost of
`e^{QD}`, and the unit-size hypothesis converts that factor into an additive
error; the `L` new nonlinear terms are each at most `e^{QD} - 1`; and the at most
`L` new centered scales are covered by the induction bounding the new
fluctuation terms, each bounded by `K(𝒫_q(T;b) + (e^{QD} - 1))`.

The constant is exhibited: `C_L = 1 + LK + (1-3^{-a})^{-1} + L`, with `K` the
constant of the induction, admissible under `λ_port ≤ 1/4`.
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

/-! ## The new centered scales -/

/-- The at most `L` new centered scales are each covered by the induction. -/
theorem propagation_centered_new [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax Crec K : ℝ}
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
    {b h L T : ℤ} (hh : 1 ≤ h) (hL : 1 ≤ L) (hb : jStar ≤ b) (hbT : b + h ≤ T)
    (hTL : T + L ≤ TMax)
    (hKbase : (3 : ℝ) ^ (a * (h : ℝ)) ≤ K)
    (hKstep : 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q * K +
        2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
          (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
            (3 : ℝ) ^ (a * (h : ℝ))) ≤ K)
    (hprof : portableProfile P Q a rhoMax q jStar b T ≤ 1) :
    ∑ j ∈ Finset.Icc (T + 1) (T + L),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + L))) *
          centeredMoment P Q q j ^ Q ≤
      ENNReal.ofReal ((L : ℝ) * K) *
        (portableProfile P Q a rhoMax q jStar b T +
          ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans zero_le_one hL
  have hterm : ∀ j ∈ Finset.Icc (T + 1) (T + L),
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + L))) *
          centeredMoment P Q q j ^ Q ≤
        ENNReal.ofReal K *
          (portableProfile P Q a rhoMax q jStar b T +
            ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hw1 : ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ)))) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_)
      have hjr : (j : ℝ) ≤ ((T + L : ℤ) : ℝ) := by exact_mod_cast hj.2
      nlinarith only [hjr, ha]
    calc ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + L))) * centeredMoment P Q q j ^ Q
        = ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ)))) *
            (ENNReal.ofReal (Real.exp (Q * detIncrement P q j (T + L))) *
              centeredMoment P Q q j ^ Q) :=
          (ofReal_mul_ofReal_mul (Real.rpow_nonneg (by norm_num) _) _ _).symm
      _ ≤ 1 * (ENNReal.ofReal K *
            (portableProfile P Q a rhoMax q jStar b T +
              ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1))) :=
          mul_le_mul' hw1 (transported_moment_le hQ ha hCrec hP hunit hq hlj hfin hmom hrec
            hh hL hb hbT hTL hKbase hKstep hprof (by omega) hj.2)
      _ = _ := one_mul _
  have hcard : (Finset.Icc (T + 1) (T + L)).card = L.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hcast : ((L.toNat : ℕ) : ℝ) = (L : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_trans zero_le_one hL)
  calc ∑ j ∈ Finset.Icc (T + 1) (T + L),
        ENNReal.ofReal ((3 : ℝ) ^ (-a * (((T + L : ℤ) : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j (T + L))) *
          centeredMoment P Q q j ^ Q
      ≤ ∑ _j ∈ Finset.Icc (T + 1) (T + L),
          ENNReal.ofReal K *
            (portableProfile P Q a rhoMax q jStar b T +
              ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((L : ℝ) * K) *
          (portableProfile P Q a rhoMax q jStar b T +
            ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast, hcast,
          ofReal_mul_ofReal_mul hL0]

/-! ## The propagation estimate -/

/-- **`e.fixed.geometry.profile.fixed.span`.**  A unit-size profile propagates
over `L` scales at the cost of a constant depending only on the data, with no
scale-independent positive error. -/
theorem portableProfile_propagation [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax Crec K : ℝ}
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
    {b h L T : ℤ} (hh : 1 ≤ h) (hL : 1 ≤ L) (hb : jStar ≤ b) (hbT : b + h ≤ T)
    (hTL : T + L ≤ TMax)
    (hKbase : (3 : ℝ) ^ (a * (h : ℝ)) ≤ K)
    (hKstep : 2 ^ (Q - 1) * Crec ^ Q * ((3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2)) ^ Q * K +
        2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q *
          (1 + Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
            (3 : ℝ) ^ (a * (h : ℝ))) ≤ K)
    (hprof : portableProfile P Q a rhoMax q jStar b T ≤ 1) :
    portableProfile P Q a rhoMax q jStar b (T + L) ≤
      ENNReal.ofReal (1 + (L : ℝ) * K + 1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
          portableProfile P Q a rhoMax q jStar b T +
        ENNReal.ofReal ((1 + (L : ℝ) * K + 1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
          (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans zero_le_one hL
  have hK0 : (0 : ℝ) ≤ K := le_trans (Real.rpow_nonneg (by norm_num) _) hKbase
  have hLK0 : (0 : ℝ) ≤ (L : ℝ) * K := mul_nonneg hL0 hK0
  have hGa0 : (0 : ℝ) ≤ 1 / (1 - (3 : ℝ) ^ (-a)) := by
    have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by
      have := geom_ratio_lt_one ha
      linarith only [this]
    positivity
  have hD0 : 0 ≤ detIncrement P q T (T + L) :=
    Recurrence.detIncrement_nonneg hP hq (le_trans hlj (by omega)) (by omega)
      (hfin T (by omega) (by omega)) (hfin (T + L) (by omega) hTL)
  have hED1 : (1 : ℝ) ≤ Real.exp (Q * detIncrement P q T (T + L)) :=
    Real.one_le_exp (mul_nonneg hQ0 hD0)
  have hED0 : (0 : ℝ) ≤ Real.exp (Q * detIncrement P q T (T + L)) - 1 := by linarith only [hED1]
  have hunionV : Finset.Icc (b + 1) T ∪ Finset.Icc (T + 1) (T + L) =
      Finset.Icc (b + 1) (T + L) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisjV : Disjoint (Finset.Icc (b + 1) T) (Finset.Icc (T + 1) (T + L)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    omega
  have hunionN : Finset.Ico b T ∪ Finset.Ico T (T + L) = Finset.Ico b (T + L) :=
    Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
  have hdisjN : Disjoint (Finset.Ico b T) (Finset.Ico T (T + L)) :=
    Finset.Ico_disjoint_Ico_consecutive b T (T + L)
  have hI := propagation_inherited (rhoMax := rhoMax) hQ0 ha hP hq hlj hfin hL hb (by omega) hTL
  have hVold := propagation_centered_old (P := P) (q := q) (Q := Q) (b := b) (T := T) (L := L)
    ha hL
  have hVnew := propagation_centered_new hQ ha hCrec hP hunit hq hlj hfin hmom hrec hh hL hb hbT
    hTL hKbase hKstep hprof
  have hNold := propagation_nonlinear_old hQ0 ha hP hq hlj hfin hL hb (by omega) hTL
  have hNnew := startup_nonlinear (a := a) hQ0 ha hP hq hlj hfin hL (by omega : jStar ≤ T) hTL
  have hPT : ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b T))) * portableHistory P Q a rhoMax q jStar b +
        (∑ j ∈ Finset.Icc (b + 1) T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
              Real.exp (Q * detIncrement P q j T)) * centeredMoment P Q q j ^ Q) +
        ∑ j ∈ Finset.Ico b T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            frakH Q (relMean P q j T)) = portableProfile P Q a rhoMax q jStar b T := by
    rw [portableProfile]
  have habs := ofReal_mul_le_add_of_le_one hED1 hprof
  have h1LK : (1 : ℝ≥0∞) + ENNReal.ofReal ((L : ℝ) * K) =
      ENNReal.ofReal (1 + (L : ℝ) * K) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hLK0]
  have herr : ENNReal.ofReal ((1 + (L : ℝ) * K) *
          (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
        ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
          (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
        ENNReal.ofReal ((L : ℝ) * (Real.exp (Q * detIncrement P q T (T + L)) - 1)) =
      ENNReal.ofReal ((1 + (L : ℝ) * K + 1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
        (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg (by linarith only [hLK0]) hED0)
        (mul_nonneg hGa0 hED0),
      ← ENNReal.ofReal_add (by nlinarith only [hLK0, hGa0, hED0]) (mul_nonneg hL0 hED0)]
    congr 1
    ring
  conv_lhs => rw [portableProfile]
  rw [← hunionV, Finset.sum_union hdisjV, ← hunionN, Finset.sum_union hdisjN]
  refine le_trans (add_le_add (add_le_add hI (add_le_add hVold hVnew))
    (add_le_add hNold hNnew)) ?_
  calc ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
              (1 + frakH Q (relMean P q b T))) * portableHistory P Q a rhoMax q jStar b) +
          (ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
              (∑ j ∈ Finset.Icc (b + 1) T,
                ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
                    Real.exp (Q * detIncrement P q j T)) * centeredMoment P Q q j ^ Q) +
            ENNReal.ofReal ((L : ℝ) * K) *
              (portableProfile P Q a rhoMax q jStar b T +
                ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1))) +
          (ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
                (∑ j ∈ Finset.Ico b T,
                  ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
                    frakH Q (relMean P q j T))) +
              ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
                (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
            ENNReal.ofReal ((L : ℝ) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1)))
      = ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L))) *
            portableProfile P Q a rhoMax q jStar b T +
          ENNReal.ofReal ((L : ℝ) * K) *
            (portableProfile P Q a rhoMax q jStar b T +
              ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
          (ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
            ENNReal.ofReal ((L : ℝ) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1))) := by
        rw [← hPT]
        ring
    _ ≤ (portableProfile P Q a rhoMax q jStar b T +
            ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
          ENNReal.ofReal ((L : ℝ) * K) *
            (portableProfile P Q a rhoMax q jStar b T +
              ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
          (ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
            ENNReal.ofReal ((L : ℝ) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1))) :=
        add_le_add (add_le_add habs le_rfl) le_rfl
    _ = ENNReal.ofReal (1 + (L : ℝ) * K) *
            (portableProfile P Q a rhoMax q jStar b T +
              ENNReal.ofReal (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
          (ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
            ENNReal.ofReal ((L : ℝ) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1))) := by
        rw [← h1LK]
        ring
    _ = ENNReal.ofReal (1 + (L : ℝ) * K) * portableProfile P Q a rhoMax q jStar b T +
          (ENNReal.ofReal ((1 + (L : ℝ) * K) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
            ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a)) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1)) +
            ENNReal.ofReal ((L : ℝ) *
              (Real.exp (Q * detIncrement P q T (T + L)) - 1))) := by
        rw [ENNReal.ofReal_mul (by linarith only [hLK0] : (0 : ℝ) ≤ 1 + (L : ℝ) * K)]
        ring
    _ = ENNReal.ofReal (1 + (L : ℝ) * K) * portableProfile P Q a rhoMax q jStar b T +
          ENNReal.ofReal ((1 + (L : ℝ) * K + 1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
            (Real.exp (Q * detIncrement P q T (T + L)) - 1)) := by rw [herr]
    _ ≤ ENNReal.ofReal (1 + (L : ℝ) * K + 1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
            portableProfile P Q a rhoMax q jStar b T +
          ENNReal.ofReal ((1 + (L : ℝ) * K + 1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ)) *
            (Real.exp (Q * detIncrement P q T (T + L)) - 1)) :=
        add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (by linarith only [hGa0, hL0])) le_rfl) le_rfl

end Window

end

end PortableHistory
end HighContrast
end Homogenization
