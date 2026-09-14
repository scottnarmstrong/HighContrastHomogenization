/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Startup

/-!
# The left rows of a unit-size profile

The propagation estimate of `p.fixed.geometry.one.grid.propagation` reaches the new centered
scales `T < s ≤ T+L` through predecessors `s-h` lying in `{T+1-h, …, T}`, and it
needs two bounds on the data at those left scales, valid when
`𝒫_q(T;b) ≤ 1`:

* the recent fluctuation terms are controlled by the profile,
  `e^{QΔ_{r,T}^q}(v_r^q)^Q ≤ C(a,h)𝒫_q(T;b)` — the term at `r` of the centered
  row of `e.scale.selection.complete.profile` carries the weight `3^{-a(T-r)}`, and
  the service hypothesis `T ≥ b+h` places `r` inside that row;
* the recent determinant losses are controlled by the profile,
  `e^{QΔ_{r,T}^q} - 1 ≤ C(Q,a,h)𝔥_Q(P_{r,T}^q) ≤ C(Q,a,h)𝒫_q(T;b)` — with
  `x = tr(P_{r,T}^q - I)` the determinant increment satisfies `Δ_{r,T}^q ≤ x`,
  because the determinant of a positive matrix is at most the exponential of its
  trace gap; the nonlinear row of a unit-size profile bounds `𝔥_Q(P_{r,T}^q)`,
  hence bounds `x`; and on that bounded interval the two scalar functions
  `e^{Qx} - 1` and `(1+x)^Q - 1` are comparable, through
  `e^{u} - 1 ≤ ue^{u}` and `(1+x)^Q ≥ 1+x`.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix ENNReal

noncomputable section

/-! ## Two elementary comparisons -/

/-- The determinant of a positive semidefinite matrix is at most the exponential
of its trace gap: each eigenvalue is at most `e^{λ-1}`. -/
theorem det_le_exp_trace_sub {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) :
    A.det ≤ Real.exp (Matrix.trace A - Fintype.card n) := by
  have hdet : A.det = ∏ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.det_eq_prod_eigenvalues
  have htr : Matrix.trace A = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  have hstep : ∀ i ∈ (Finset.univ : Finset n),
      hA.isHermitian.eigenvalues i ≤ Real.exp (hA.isHermitian.eigenvalues i - 1) := by
    intro i _
    have h := Real.add_one_le_exp (hA.isHermitian.eigenvalues i - 1)
    linarith only [h]
  have hprod := Finset.prod_le_prod (fun i _ => hA.eigenvalues_nonneg i) hstep
  rw [← Real.exp_sum] at hprod
  rw [hdet, htr]
  refine le_trans hprod (le_of_eq ?_)
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The excess of an exponential over one, against its own linear factor. -/
theorem exp_sub_one_le_mul_exp {t : ℝ} : Real.exp t - 1 ≤ t * Real.exp t := by
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have h := Real.add_one_le_exp (-t)
  rw [Real.exp_neg] at h
  have h2 := mul_le_mul_of_nonneg_right h hpos.le
  rw [inv_mul_cancel₀ (ne_of_gt hpos)] at h2
  linarith only [h2]

/-- **The scalar comparison behind the bound on the recent determinant losses.**  On
the interval where the gain `(1+x)^Q - 1` is bounded by `G`, the exponential gain
`e^{QD}-1` of any `D ≤ x` is comparable to it, with a constant depending only on
`Q` and `G`. -/
theorem exp_sub_one_le_rpow_sub_one {Q x G D : ℝ} (hQ : 1 ≤ Q) (hx0 : 0 ≤ x)
    (hxG : (1 + x) ^ Q - 1 ≤ G) (hD : D ≤ x) :
    Real.exp (Q * D) - 1 ≤ Q * Real.exp (Q * ((1 + G) ^ Q⁻¹ - 1)) * ((1 + x) ^ Q - 1) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have h1x : (1 : ℝ) ≤ 1 + x := by linarith only [hx0]
  have hxpow : (1 + x) ^ Q ≤ 1 + G := by linarith only [hxG]
  have hxle : 1 + x ≤ (1 + G) ^ Q⁻¹ := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith only [h1x]) Q) hxpow
      (by positivity : (0 : ℝ) ≤ Q⁻¹)
    rwa [← Real.rpow_mul (by linarith only [h1x]), mul_inv_cancel₀ (ne_of_gt hQ0),
      Real.rpow_one] at h1
  have hX0 : x ≤ (1 + G) ^ Q⁻¹ - 1 := by linarith only [hxle]
  have hxfrak : x ≤ (1 + x) ^ Q - 1 := by
    have h1 : (1 + x) ^ (1 : ℝ) ≤ (1 + x) ^ Q := Real.rpow_le_rpow_of_exponent_le h1x hQ
    rw [Real.rpow_one] at h1
    linarith only [h1]
  have h1 : Real.exp (Q * D) ≤ Real.exp (Q * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hD hQ0.le)
  have h2 : Real.exp (Q * x) - 1 ≤ Q * x * Real.exp (Q * x) := exp_sub_one_le_mul_exp
  have h3 : Real.exp (Q * x) ≤ Real.exp (Q * ((1 + G) ^ Q⁻¹ - 1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hX0 hQ0.le)
  have hQx0 : (0 : ℝ) ≤ Q * x := mul_nonneg hQ0.le hx0
  have h4 : Q * x * Real.exp (Q * x) ≤ Q * x * Real.exp (Q * ((1 + G) ^ Q⁻¹ - 1)) :=
    mul_le_mul_of_nonneg_left h3 hQx0
  have h5 : Q * x * Real.exp (Q * ((1 + G) ^ Q⁻¹ - 1)) ≤
      Q * ((1 + x) ^ Q - 1) * Real.exp (Q * ((1 + G) ^ Q⁻¹ - 1)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxfrak hQ0.le) (Real.exp_pos _).le
  linarith only [h1, h2, h4, h5]

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-! ## The determinant increment against the trace gap -/

/-- **`Δ_{r,T}^q ≤ tr(P_{r,T}^q - I)`.**  The relative mean is positive, so its
determinant `e^{Δ_{r,T}^q}` is at most the exponential of its trace gap. -/
theorem detIncrement_le_trace_relMean [NeZero d] [IsProbabilityMeasure P]
    (hq : IsRoundedGrid l q)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {r T : ℤ} (hr : jStar ≤ r) (hrT : r ≤ T) (hT : T ≤ TMax) :
    detIncrement P q r T ≤ Matrix.trace (toFullBlockMat (relMean P q r T) - 1) := by
  have hpdr : (toFullBlockMat (adaptedMean P q r)).PosDef :=
    posDef_adaptedMean_window hq hfin hr (le_trans hrT hT)
  have hpdT : (toFullBlockMat (adaptedMean P q T)).PosDef :=
    posDef_adaptedMean_window hq hfin (le_trans hr hrT) hT
  have hps : (toFullBlockMat (relMean P q r T)).PosSemidef := by
    rw [Recurrence.toFullBlockMat_relMean]
    exact (posDef_normalize hpdr hpdT).posSemidef
  have hdet : (toFullBlockMat (relMean P q r T)).det = Real.exp (detIncrement P q r T) := by
    rw [Recurrence.toFullBlockMat_relMean]
    exact Recurrence.det_normalize_eq_exp hpdr hpdT
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  have hle := det_le_exp_trace_sub hps
  rw [hdet, hcard] at hle
  rw [Matrix.trace_sub, Matrix.trace_one, hcard]
  exact Real.exp_le_exp.mp hle

/-! ## The left centered row -/

/-- **The recent fluctuation terms are controlled by the profile.**  A centered scale of the covered
span is one of the terms of the centered row of the profile, whose weight is at
least `3^{-ah}` there. -/
theorem exp_mul_centeredMoment_le [NeZero d] {Q a rhoMax : ℝ} (ha : 0 < a)
    {b h T r : ℤ} (hbT : b + h ≤ T) (hr : T + 1 - h ≤ r) (hrT : r ≤ T) :
    ENNReal.ofReal (Real.exp (Q * detIncrement P q r T)) * centeredMoment P Q q r ^ Q ≤
      ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
        portableProfile P Q a rhoMax q jStar b T := by
  have hmem : r ∈ Finset.Icc (b + 1) T := by
    rw [Finset.mem_Icc]
    omega
  have hVterm : ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
        Real.exp (Q * detIncrement P q r T)) * centeredMoment P Q q r ^ Q ≤
      portableProfile P Q a rhoMax q jStar b T := by
    rw [portableProfile]
    refine le_trans (Finset.single_le_sum
      (f := fun j : ℤ => ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
        Real.exp (Q * detIncrement P q j T)) * centeredMoment P Q q j ^ Q)
      (fun i _ => zero_le) hmem) ?_
    exact le_trans (self_le_add_left _ _) (self_le_add_right _ _)
  have hprod : (3 : ℝ) ^ (a * ((T : ℝ) - (r : ℝ))) *
      ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) * Real.exp (Q * detIncrement P q r T)) =
      Real.exp (Q * detIncrement P q r T) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show a * ((T : ℝ) - (r : ℝ)) + -a * ((T : ℝ) - (r : ℝ)) = 0 by ring, Real.rpow_zero,
      one_mul]
  have hexpo : a * ((T : ℝ) - (r : ℝ)) ≤ a * (h : ℝ) := by
    have hcast : (T : ℝ) - (r : ℝ) ≤ (h : ℝ) := by
      have hz : (T : ℤ) - r ≤ h := by omega
      have hc : ((T - r : ℤ) : ℝ) ≤ ((h : ℤ) : ℝ) := by exact_mod_cast hz
      push_cast at hc
      linarith only [hc]
    exact mul_le_mul_of_nonneg_left hcast ha.le
  calc ENNReal.ofReal (Real.exp (Q * detIncrement P q r T)) * centeredMoment P Q q r ^ Q
      = ENNReal.ofReal ((3 : ℝ) ^ (a * ((T : ℝ) - (r : ℝ)))) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (r : ℝ))) *
              Real.exp (Q * detIncrement P q r T)) * centeredMoment P Q q r ^ Q) := by
        rw [ofReal_mul_ofReal_mul (Real.rpow_nonneg (by norm_num) _), hprod]
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (a * ((T : ℝ) - (r : ℝ)))) *
          portableProfile P Q a rhoMax q jStar b T := mul_le_mul' le_rfl hVterm
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
          portableProfile P Q a rhoMax q jStar b T :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpo)) le_rfl

/-! ## The left determinant row -/

/-- The gain at a left scale of a unit-size profile is bounded by a constant
depending only on `a` and `h`. -/
theorem frakH_le_of_portableProfile_le_one [NeZero d] {Q a rhoMax : ℝ} (ha : 0 < a)
    {b h T r : ℤ} (hbT : b + h ≤ T) (hr : T + 1 - h ≤ r) (hrT : r < T) :
    ENNReal.ofReal (frakH Q (relMean P q r T)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
        portableProfile P Q a rhoMax q jStar b T := by
  have hmem : r ∈ Finset.Ico b T := by
    rw [Finset.mem_Ico]
    omega
  have hNterm : ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (r : ℝ))) *
        frakH Q (relMean P q r T)) ≤ portableProfile P Q a rhoMax q jStar b T := by
    rw [portableProfile]
    refine le_trans (Finset.single_le_sum
      (f := fun j : ℤ => ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
        frakH Q (relMean P q j T))) (fun i _ => zero_le) hmem) ?_
    exact self_le_add_left _ _
  have hprod : (3 : ℝ) ^ (a * ((T : ℝ) - 1 - (r : ℝ))) *
      ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (r : ℝ))) * frakH Q (relMean P q r T)) =
      frakH Q (relMean P q r T) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show a * ((T : ℝ) - 1 - (r : ℝ)) + -a * ((T : ℝ) - 1 - (r : ℝ)) = 0 by ring,
      Real.rpow_zero, one_mul]
  have hexpo : a * ((T : ℝ) - 1 - (r : ℝ)) ≤ a * (h : ℝ) := by
    have hcast : (T : ℝ) - 1 - (r : ℝ) ≤ (h : ℝ) := by
      have hz : (T : ℤ) - 1 - r ≤ h := by omega
      have hc : ((T - 1 - r : ℤ) : ℝ) ≤ ((h : ℤ) : ℝ) := by exact_mod_cast hz
      push_cast at hc
      linarith only [hc]
    exact mul_le_mul_of_nonneg_left hcast ha.le
  calc ENNReal.ofReal (frakH Q (relMean P q r T))
      = ENNReal.ofReal ((3 : ℝ) ^ (a * ((T : ℝ) - 1 - (r : ℝ)))) *
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (r : ℝ))) *
            frakH Q (relMean P q r T)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hprod]
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (a * ((T : ℝ) - 1 - (r : ℝ)))) *
          portableProfile P Q a rhoMax q jStar b T := mul_le_mul' le_rfl hNterm
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
          portableProfile P Q a rhoMax q jStar b T :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpo)) le_rfl

/-- **The recent determinant losses are controlled by the profile.**  At a left scale of a
unit-size profile the excess of `e^{QΔ_{r,T}^q}` over one is bounded by the
profile, with a constant depending only on `Q`, `a` and `h`. -/
theorem exp_detIncrement_sub_one_le [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ}
    (hQ : 1 ≤ Q) (ha : 0 < a)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b h T r : ℤ} (hb : jStar ≤ b) (hbT : b + h ≤ T) (hT : T ≤ TMax)
    (hr : T + 1 - h ≤ r) (hrT : r ≤ T)
    (hprof : portableProfile P Q a rhoMax q jStar b T ≤ 1) :
    ENNReal.ofReal (Real.exp (Q * detIncrement P q r T) - 1) ≤
      ENNReal.ofReal (Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
          (3 : ℝ) ^ (a * (h : ℝ))) *
        portableProfile P Q a rhoMax q jStar b T := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  rcases eq_or_lt_of_le hrT with heq | hlt
  · rw [heq, detIncrement_self, mul_zero, Real.exp_zero, sub_self, ENNReal.ofReal_zero]
    exact zero_le
  · have hjs : jStar ≤ r := by omega
    have hfrak : ENNReal.ofReal (frakH Q (relMean P q r T)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
          portableProfile P Q a rhoMax q jStar b T :=
      frakH_le_of_portableProfile_le_one ha hbT hr hlt
    have hfrak1 : ENNReal.ofReal (frakH Q (relMean P q r T)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) := by
      refine le_trans hfrak ?_
      calc ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
            portableProfile P Q a rhoMax q jStar b T
          ≤ ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) * 1 := mul_le_mul' le_rfl hprof
        _ = ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) := mul_one _
    have hfrakr : frakH Q (relMean P q r T) ≤ (3 : ℝ) ^ (a * (h : ℝ)) :=
      (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (by norm_num) _)).mp hfrak1
    have hx0 : 0 ≤ Matrix.trace (toFullBlockMat (relMean P q r T) - 1) :=
      trace_relMean_sub_one_nonneg hP hq hlj hfin hjs hrT hT
    have hfx : frakH Q (relMean P q r T) =
        (1 + Matrix.trace (toFullBlockMat (relMean P q r T) - 1)) ^ Q - 1 := frakH_eq_rpow Q _
    have hkey := exp_sub_one_le_rpow_sub_one (D := detIncrement P q r T)
      (G := (3 : ℝ) ^ (a * (h : ℝ))) hQ hx0 (by rw [← hfx]; exact hfrakr)
      (detIncrement_le_trace_relMean hq hfin hjs hrT hT)
    rw [← hfx] at hkey
    have hC0 : (0 : ℝ) ≤ Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) :=
      mul_nonneg hQ0.le (Real.exp_pos _).le
    calc ENNReal.ofReal (Real.exp (Q * detIncrement P q r T) - 1)
        ≤ ENNReal.ofReal (Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
            frakH Q (relMean P q r T)) := ENNReal.ofReal_le_ofReal hkey
      _ = ENNReal.ofReal (Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1))) *
            ENNReal.ofReal (frakH Q (relMean P q r T)) := ENNReal.ofReal_mul hC0
      _ ≤ ENNReal.ofReal (Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (a * (h : ℝ))) *
              portableProfile P Q a rhoMax q jStar b T) := mul_le_mul' le_rfl hfrak
      _ = ENNReal.ofReal (Q * Real.exp (Q * ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ Q⁻¹ - 1)) *
            (3 : ℝ) ^ (a * (h : ℝ))) * portableProfile P Q a rhoMax q jStar b T :=
          ofReal_mul_ofReal_mul hC0 _ _

end Window

end

end PortableHistory
end HighContrast
end Homogenization
