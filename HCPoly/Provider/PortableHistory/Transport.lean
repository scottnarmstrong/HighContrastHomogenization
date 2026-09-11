/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.TraceGap

/-!
# Transport of the nonlinear history between terminal normalizations

The proof of `p.fixed.geometry.one.grid.propagation` opens by recording the effect of changing
the terminal normalization on the gain `𝔥_Q(P_{j,T}^q)`.  Three displays are
proved here, on the bounded window the proposition's guards control:

* `e.two.grid.mean.split`,
  `𝔥_Q(P_{j,t}) ≤ (1 + 𝔥_Q(P_{s,t}))𝔥_Q(P_{j,s}) + 𝔥_Q(P_{s,t})`;
* the determinant bound for the mean penalty,
  `1 + 𝔥_Q(P_{s,t}) ≤ e^{QΔ_{s,t}}`;
* the exponential transport of the mean penalty,
  `𝔥_Q(P_{j,t}) ≤ e^{QΔ_{s,t}}𝔥_Q(P_{j,s}) + (e^{QΔ_{s,t}} - 1)`.

All three are the `Q`-th power of a scalar statement about the trace gaps: the
first of the printed trace step, the second of the bound
`|P_{s,t}| ≤ 1 + tr(P_{s,t} - I) ≤ det P_{s,t} = e^{Δ_{s,t}}` already available at
the adapted means.  The determinant increment is additive in the middle scale,
which is the bookkeeping the later displays use.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The determinant increment -/

/-- **The determinant increment is additive in the middle scale.** -/
theorem detIncrement_add (P : Measure (CoeffSpace d)) (q : Mat d) (j s t : ℤ) :
    detIncrement P q j t = detIncrement P q j s + detIncrement P q s t := by
  simp only [detIncrement]
  ring

/-- The determinant increment vanishes on a degenerate pair of scales. -/
theorem detIncrement_self (P : Measure (CoeffSpace d)) (q : Mat d) (j : ℤ) :
    detIncrement P q j j = 0 := by
  simp only [detIncrement, sub_self]

/-! ## The trace gap of a relative mean -/

/-- The trace gap `tr(P - I)` of a doubled block is the printed
`tr(P) - 2d`. -/
theorem blockTrace_sub_two_mul (Pm : BlockMat d) :
    blockTrace Pm - 2 * (d : ℝ) = Matrix.trace (toFullBlockMat Pm - 1) := by
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  rw [Matrix.trace_sub, Matrix.trace_one, hcard]
  rfl

/-- The gain `𝔥_Q` read on the trace gap of the flattened block. -/
theorem frakH_eq_rpow (Q : ℝ) (Pm : BlockMat d) :
    frakH Q Pm = (1 + Matrix.trace (toFullBlockMat Pm - 1)) ^ Q - 1 := by
  simp only [frakH, blockTrace_sub_two_mul]

/-! ## The window hypotheses -/

section Window

variable {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- **The mean order on the bounded window.**  The adapted means decrease with
the scale, which is the opening sentence of the proof of
`p.fixed.geometry.one.grid.propagation`. -/
theorem adaptedMean_le_window [NeZero d] (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    toFullBlockMat (adaptedMean P q T) ≤ toFullBlockMat (adaptedMean P q j) :=
  Recurrence.toFullBlockMat_adaptedMean_le hP hq (le_trans hlj hj) hjT
    (hfin j hj (le_trans hjT hT)) (hfin T (le_trans hj hjT) hT)

/-- The adapted mean is positive definite on the bounded window. -/
theorem posDef_adaptedMean_window [IsProbabilityMeasure P] (hq : IsRoundedGrid l q)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j : ℤ} (hj : jStar ≤ j) (hjT : j ≤ TMax) :
    (toFullBlockMat (adaptedMean P q j)).PosDef :=
  Recurrence.posDef_toFullBlockMat_adaptedMean hq j (hfin j hj hjT)

/-- **`I ≤ P_{j,T}^q` on the bounded window**, on the flattened carrier. -/
theorem one_le_relMean_window [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    (1 : FullBlockMat d) ≤ toFullBlockMat (relMean P q j T) := by
  rw [Recurrence.toFullBlockMat_relMean]
  exact Recurrence.one_le_normalize (posDef_adaptedMean_window hq hfin (le_trans hj hjT) hT)
    (adaptedMean_le_window hP hq hlj hfin hj hjT hT)

/-- The trace gap of a relative mean is nonnegative on the bounded window. -/
theorem trace_relMean_sub_one_nonneg [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    0 ≤ Matrix.trace (toFullBlockMat (relMean P q j T) - 1) :=
  trace_sub_one_nonneg (one_le_relMean_window hP hq hlj hfin hj hjT hT)

/-- **The gain of a relative mean is nonnegative on the bounded window.** -/
theorem frakH_relMean_nonneg [NeZero d] [IsProbabilityMeasure P] {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    0 ≤ frakH Q (relMean P q j T) := by
  have hgap := trace_relMean_sub_one_nonneg hP hq hlj hfin hj hjT hT
  have hone : (1 : ℝ) ≤ 1 + Matrix.trace (toFullBlockMat (relMean P q j T) - 1) := by
    linarith only [hgap]
  have hpow : (1 : ℝ) ≤ (1 + Matrix.trace (toFullBlockMat (relMean P q j T) - 1)) ^ Q := by
    have := Real.rpow_le_rpow zero_le_one hone hQ
    rwa [Real.one_rpow] at this
  rw [frakH_eq_rpow]
  linarith only [hpow]

/-- **The multiplicative form of `e.two.grid.mean.split`.**
The trace step at the power `Q`. -/
theorem one_add_frakH_mul_le [NeZero d] [IsProbabilityMeasure P] {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j s t : ℤ} (hj : jStar ≤ j) (hjs : j ≤ s) (hst : s ≤ t) (ht : t ≤ TMax) :
    1 + frakH Q (relMean P q j t) ≤
      (1 + frakH Q (relMean P q j s)) * (1 + frakH Q (relMean P q s t)) := by
  have hs : jStar ≤ s := le_trans hj hjs
  have hjt : j ≤ t := le_trans hjs hst
  have hsT : s ≤ TMax := le_trans hst ht
  have hkey : 1 + Matrix.trace (toFullBlockMat (relMean P q j t) - 1) ≤
      (1 + Matrix.trace (toFullBlockMat (relMean P q j s) - 1)) *
        (1 + Matrix.trace (toFullBlockMat (relMean P q s t) - 1)) := by
    rw [Recurrence.toFullBlockMat_relMean, Recurrence.toFullBlockMat_relMean, Recurrence.toFullBlockMat_relMean]
    exact one_add_trace_normalize_le (posDef_adaptedMean_window hq hfin hs hsT)
      (posDef_adaptedMean_window hq hfin (le_trans hs hst) ht)
      (adaptedMean_le_window hP hq hlj hfin hj hjs hsT)
      (adaptedMean_le_window hP hq hlj hfin hs hst ht)
  have hjs0 := trace_relMean_sub_one_nonneg hP hq hlj hfin hj hjs hsT
  have hst0 := trace_relMean_sub_one_nonneg hP hq hlj hfin hs hst ht
  have hjt0 := trace_relMean_sub_one_nonneg hP hq hlj hfin hj hjt ht
  have hpow : (1 + Matrix.trace (toFullBlockMat (relMean P q j t) - 1)) ^ Q ≤
      (1 + Matrix.trace (toFullBlockMat (relMean P q j s) - 1)) ^ Q *
        (1 + Matrix.trace (toFullBlockMat (relMean P q s t) - 1)) ^ Q := by
    have hmul := Real.rpow_le_rpow (by linarith only [hjt0]) hkey hQ
    rwa [Real.mul_rpow (by linarith only [hjs0]) (by linarith only [hst0])] at hmul
  rw [frakH_eq_rpow, frakH_eq_rpow, frakH_eq_rpow]
  have hexpand : (1 + ((1 + Matrix.trace (toFullBlockMat (relMean P q j s) - 1)) ^ Q - 1)) *
      (1 + ((1 + Matrix.trace (toFullBlockMat (relMean P q s t) - 1)) ^ Q - 1)) =
      (1 + Matrix.trace (toFullBlockMat (relMean P q j s) - 1)) ^ Q *
        (1 + Matrix.trace (toFullBlockMat (relMean P q s t) - 1)) ^ Q := by
    ring
  rw [hexpand]
  linarith only [hpow]

/-- **`e.two.grid.mean.split`.**  Changing the terminal
normalization from `s` to `t` multiplies the gain at `j` by
`1 + 𝔥_Q(P_{s,t})` and adds `𝔥_Q(P_{s,t})`. -/
theorem frakH_transport_nonlinear [NeZero d] [IsProbabilityMeasure P] {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j s t : ℤ} (hj : jStar ≤ j) (hjs : j ≤ s) (hst : s ≤ t) (ht : t ≤ TMax) :
    frakH Q (relMean P q j t) ≤
      (1 + frakH Q (relMean P q s t)) * frakH Q (relMean P q j s) +
        frakH Q (relMean P q s t) := by
  have hmul := one_add_frakH_mul_le hQ hP hq hlj hfin hj hjs hst ht
  have hexpand : (1 + frakH Q (relMean P q j s)) * (1 + frakH Q (relMean P q s t)) =
      (1 + frakH Q (relMean P q s t)) * frakH Q (relMean P q j s) +
        frakH Q (relMean P q s t) + 1 := by
    ring
  rw [hexpand] at hmul
  linarith only [hmul]

/-- **The determinant bound for the mean penalty.**  The gain of a relative
mean is dominated by the exponential of its determinant increment. -/
theorem one_add_frakH_le_exp [NeZero d] [IsProbabilityMeasure P] {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {s t : ℤ} (hs : jStar ≤ s) (hst : s ≤ t) (ht : t ≤ TMax) :
    1 + frakH Q (relMean P q s t) ≤ Real.exp (Q * detIncrement P q s t) := by
  obtain ⟨-, -, -, -, htr⟩ := Recurrence.determinant_transport_adaptedMean hP hq
    (le_trans hlj hs) hst (hfin s hs (le_trans hst ht)) (hfin t (le_trans hs hst) ht)
  have hgap : 1 + Matrix.trace (toFullBlockMat (relMean P q s t) - 1) ≤
      Real.exp (detIncrement P q s t) := by
    rw [← blockTrace_sub_two_mul]
    linarith only [htr]
  have hst0 := trace_relMean_sub_one_nonneg hP hq hlj hfin hs hst ht
  have hpow := Real.rpow_le_rpow (by linarith only [hst0]) hgap hQ
  rw [frakH_eq_rpow, mul_comm Q (detIncrement P q s t), Real.exp_mul]
  linarith only [hpow]

/-- **The exponential transport of the mean penalty.**  The exponential form of
the transport display: no scale-independent error survives. -/
theorem frakH_transport_exponential [NeZero d] [IsProbabilityMeasure P] {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j s t : ℤ} (hj : jStar ≤ j) (hjs : j ≤ s) (hst : s ≤ t) (ht : t ≤ TMax) :
    frakH Q (relMean P q j t) ≤
      Real.exp (Q * detIncrement P q s t) * frakH Q (relMean P q j s) +
        (Real.exp (Q * detIncrement P q s t) - 1) := by
  have hs : jStar ≤ s := le_trans hj hjs
  have hsT : s ≤ TMax := le_trans hst ht
  have hnl := frakH_transport_nonlinear hQ hP hq hlj hfin hj hjs hst ht
  have hdet := one_add_frakH_le_exp hQ hP hq hlj hfin hs hst ht
  have hjs0 := frakH_relMean_nonneg hQ hP hq hlj hfin hj hjs hsT
  have hmul : (1 + frakH Q (relMean P q s t)) * frakH Q (relMean P q j s) ≤
      Real.exp (Q * detIncrement P q s t) * frakH Q (relMean P q j s) :=
    mul_le_mul_of_nonneg_right hdet hjs0
  linarith only [hnl, hmul, hdet]

end Window

end

end PortableHistory
end HighContrast
end Homogenization
