import HCPoly.Entry.Analysis.MeanPenaltyBounds
import HCPoly.Entry.Analysis.ScalarMomentInequalities
import HCPoly.Entry.Analysis.SchattenSpectral
import HCPoly.Entry.Annealed.AveragingTransport
import HCPoly.Entry.Annealed.LogDetOrder
import HCPoly.Entry.Annealed.MatrixAveraging
import HCPoly.Entry.Annealed.MeanOrder
import HCPoly.Entry.Annealed.Normalization
import HCPoly.Entry.Geometry.RoundedGrid
import HCPoly.Entry.Multiscale.DriftAdvance
import HCPoly.Entry.Multiscale.SelectionExponentBounds
import HCPoly.Entry.Setup.CoarseEllipticityDagger
import HCPoly.Entry.Setup.Profile
import HCPoly.Entry.Setup.Stationarity
import HCPoly.Entry.Setup.UnitRange
import HCPoly.Entry.Source.BoundedWindowFiniteness
import HCPoly.Entry.ParentChildRecurrence

/-!
# Printed exponent and coefficient arithmetic

Group A of the printed proof (`p.fixed.geometry.one.grid.propagation`): the numeric facts about
`Q = 𝒬(d,γ)`, the contraction, span and averaging coefficients, the elementary
exponential inequalities and the geometric profile weights.

Part of the proof of the statement in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of the group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
module `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group A. The printed exponent and coefficient arithmetic (`p.fixed.geometry.one.grid.propagation`) -/

/-- `Q ≥ 12` for `d ≥ 2` and `γ ∈ [0,1)` (`p.fixed.geometry.one.grid.propagation`). -/
theorem bigQ_twelve_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    12 ≤ bigQ d γ := by
  have hlow : (12 : ℝ) ≤ (4 : ℝ) * ((d : ℝ) + 1) := by
    have hd' : (2 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast hd
    linarith only [hd']
  have hmul : (12 : ℝ) ≤ (↑(bigQ d γ) * (1 - γ)) := by
    exact le_trans hlow (bigQ_mul_one_sub_ge d hd γ hγ)
  have hmul_le : (↑(bigQ d γ) * (1 - γ)) ≤ (↑(bigQ d γ) : ℝ) := by
    have hγle : (1 - γ) ≤ (1 : ℝ) := sub_le_self 1 hγ.1
    have hq_nonneg : (0 : ℝ) ≤ (↑(bigQ d γ) : ℝ) := by
      exact_mod_cast (Nat.zero_le (bigQ d γ))
    calc
      (↑(bigQ d γ) * (1 - γ)) ≤ (↑(bigQ d γ) * 1) := mul_le_mul_of_nonneg_left hγle hq_nonneg
      _ = (↑(bigQ d γ) : ℝ) := by simp
  exact_mod_cast (le_trans hmul hmul_le)

/-- `(1-γ)h ≥ 2(1-γ)Q ≥ 8(d+1)` for every natural `h ≥ 2Q` (`p.fixed.geometry.one.grid.propagation`). -/
theorem one_sub_gamma_mul_span_ge (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (h : ℕ) (hh : 2 * bigQ d γ ≤ h) :
    8 * ((d : ℝ) + 1) ≤ (1 - γ) * (h : ℝ) := by
  have hγ' : (0 : ℝ) ≤ 1 - γ := sub_nonneg.mpr (le_of_lt hγ.2)
  have h2Q_le_h' : ((2 * bigQ d γ : ℕ) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast hh
  have h2Q_le_h : (2 : ℝ) * (bigQ d γ : ℝ) ≤ (h : ℝ) := by
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h2Q_le_h'
  have hbig : 4 * ((d : ℝ) + 1) ≤ (bigQ d γ : ℝ) * (1 - γ) :=
    bigQ_mul_one_sub_ge d hd γ hγ
  have hbig2 : 8 * ((d : ℝ) + 1) ≤ 2 * ((bigQ d γ : ℝ) * (1 - γ)) := by
    linarith only [hbig]
  have hmult : (2 : ℝ) * ((bigQ d γ : ℝ) * (1 - γ)) ≤ (1 - γ) * (h : ℝ) := by
    calc
      (2 : ℝ) * ((bigQ d γ : ℝ) * (1 - γ))
          = ((2 : ℝ) * (bigQ d γ : ℝ)) * (1 - γ) := by ring
      _ ≤ (h : ℝ) * (1 - γ) := mul_le_mul_of_nonneg_right h2Q_le_h hγ'
      _ = (1 - γ) * (h : ℝ) := by ring
  exact le_trans hbig2 hmult

/-- `3^{-⅛(1-γ)h} ≤ 3^{-3} < 1/8` for every natural `h ≥ 2Q` (`p.fixed.geometry.one.grid.propagation`).  This is the
drift half of the contraction. -/
theorem three_rpow_neg_eighth_span_lt (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (h : ℕ) (hh : 2 * bigQ d γ ≤ h) :
    (3 : ℝ) ^ (-((1 - γ) / 8) * (h : ℝ)) < 1 / 8 := by
  have key : (1 - γ) * (h : ℝ) ≥ 8 * (↑d + 1) :=
    one_sub_gamma_mul_span_ge d hd γ hγ h hh
  have d_bound : (↑d : ℝ) ≥ 2 := by exact_mod_cast hd
  have exp_bound : -((1 - γ) / 8) * (h : ℝ) ≤ -3 := by nlinarith only [key, d_bound]
  have rpow_bound : (3 : ℝ) ^ (-((1 - γ) / 8) * (h : ℝ)) ≤ 3 ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) exp_bound
  have three_neg_three : (3 : ℝ) ^ (-3 : ℝ) = 1 / 27 := by
    rw [Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))]
    norm_num
  calc (3 : ℝ) ^ (-((1 - γ) / 8) * (h : ℝ))
      ≤ 3 ^ (-3 : ℝ) := rpow_bound
    _ = 1 / 27 := three_neg_three
    _ < 1 / 8 := by norm_num

/-- `2Q·3^{-d(Q-1)} ≤ 1/3` (`p.fixed.geometry.one.grid.propagation`). -/
theorem two_bigQ_mul_three_rpow_le_third (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    2 * (bigQ d γ : ℝ) * (3 : ℝ) ^ (-(d : ℝ) * ((bigQ d γ : ℝ) - 1)) ≤ 1 / 3 := by
  have hQ12 : 12 ≤ bigQ d γ := bigQ_twelve_le d hd γ hγ
  have hQ1 : 1 ≤ bigQ d γ := le_trans (by norm_num : (1:ℕ) ≤ 12) hQ12
  have haux : ∀ n : ℕ, 12 ≤ n → 6 * n ≤ 3 ^ (2 * (n - 1)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have e1 : 2 * (n + 1 - 1) = 2 * (n - 1) + 2 := by omega
      have h9 : (3:ℕ) ^ 2 = 9 := by norm_num
      rw [e1, pow_add, h9]
      nlinarith only [ih, hn]
  have h1 : 2 * (bigQ d γ - 1) ≤ d * (bigQ d γ - 1) :=
    Nat.mul_le_mul hd (le_refl (bigQ d γ - 1))
  have h2 : (3:ℕ) ^ (2 * (bigQ d γ - 1)) ≤ 3 ^ (d * (bigQ d γ - 1)) :=
    Nat.pow_le_pow_right (by norm_num) h1
  have h3 : 6 * bigQ d γ ≤ 3 ^ (2 * (bigQ d γ - 1)) := haux (bigQ d γ) hQ12
  have hkey : 6 * bigQ d γ ≤ 3 ^ (d * (bigQ d γ - 1)) := le_trans h3 h2
  have hkeyR : (6 * (bigQ d γ : ℝ)) ≤ (3:ℝ) ^ (d * (bigQ d γ - 1)) := by exact_mod_cast hkey
  have hcast : ((bigQ d γ : ℝ) - 1) = ((bigQ d γ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hQ1, Nat.cast_one]
  have hexp : -(d : ℝ) * ((bigQ d γ : ℝ) - 1) = -(((d * (bigQ d γ - 1) : ℕ) : ℝ)) := by
    rw [hcast]; push_cast; ring
  rw [hexp, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
  have hpos : (0:ℝ) < (3:ℝ) ^ (d * (bigQ d γ - 1)) := by positivity
  have hstep : 6 * (bigQ d γ : ℝ) * ((3:ℝ) ^ (d * (bigQ d γ - 1)))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hkeyR (le_of_lt (inv_pos.mpr hpos))
    rwa [mul_inv_cancel₀ (ne_of_gt hpos)] at h
  nlinarith only [hstep]

/-- The printed contraction coefficient
`3^{-¼(1-γ)h} + 2^{Q-1}(3^dQ)^Q 3^{-Qdh/2} ≤ 3^{-6} + ½·3^{-12} < 1/8`, for **every** natural
`h ≥ 2Q` (`p.fixed.geometry.one.grid.propagation`). -/
theorem contraction_coefficient_lt (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (h : ℕ) (hh : 2 * bigQ d γ ≤ h) :
    (3 : ℝ) ^ (-((1 - γ) / 4) * (h : ℝ)) +
        (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
          (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ)) < 1 / 8 := by
  set Q : ℕ := bigQ d γ with hQdef
  have hspan := one_sub_gamma_mul_span_ge d hd γ hγ h hh
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hspan24 : (24 : ℝ) ≤ (1 - γ) * (h : ℝ) := by
    nlinarith only [hspan, hdR]
  have hfirst_exp : -((1 - γ) / 4) * (h : ℝ) ≤ (-6 : ℝ) := by
    linarith only [hspan24]
  have hfirst :
      (3 : ℝ) ^ (-((1 - γ) / 4) * (h : ℝ)) ≤ (3 : ℝ) ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hfirst_exp
  have hQ12 : 12 ≤ Q := by
    simpa [hQdef] using bigQ_twelve_le d hd γ hγ
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ12
  have hhNat : 2 * Q ≤ h := by
    simpa [hQdef] using hh
  have hhR : (2 : ℝ) * (Q : ℝ) ≤ h := by exact_mod_cast hhNat
  have hprod : (d : ℝ) * (Q : ℝ) ^ 2 ≤ ((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ) := by
    calc
      (d : ℝ) * (Q : ℝ) ^ 2 = ((Q : ℝ) * (d : ℝ) / 2) * ((2 : ℝ) * (Q : ℝ)) := by ring
      _ ≤ ((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ) := by
        exact mul_le_mul_of_nonneg_left hhR (by positivity)
  have hsecond_exp :
      -((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ) ≤
        -(d : ℝ) * (Q : ℝ) ^ 2 := by
    nlinarith only [hprod]
  have hpow_second :
      (3 : ℝ) ^ (-((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ)) ≤
        (3 : ℝ) ^ (-(d : ℝ) * (Q : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hsecond_exp
  have hcoeff_nonneg :
      0 ≤ (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q := by
    positivity
  have hsecond_to_span :
      (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
          (3 : ℝ) ^ (-((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ)) ≤
        (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
          (3 : ℝ) ^ (-(d : ℝ) * (Q : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hpow_second hcoeff_nonneg
  have hA_le :
      2 * (Q : ℝ) * (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1)) ≤ 1 / 3 := by
    simpa [hQdef] using two_bigQ_mul_three_rpow_le_third d hd γ hγ
  have hA_pow :
      (2 * (Q : ℝ) * (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1))) ^ Q ≤
        (1 / 3 : ℝ) ^ Q := by
    gcongr
  have hthird : (1 / 3 : ℝ) ^ Q ≤ (1 / 3 : ℝ) ^ 12 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hQ12
  have hspan_alg :
      (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
          (3 : ℝ) ^ (-(d : ℝ) * (Q : ℝ) ^ 2) =
        (1 / 2 : ℝ) * (2 * (Q : ℝ) *
          (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1))) ^ Q := by
    have h2 : (2 : ℝ) ^ (Q - 1) = (1 / 2 : ℝ) * (2 : ℝ) ^ Q := by
      rw [← Nat.succ_pred_eq_of_pos hQpos]
      simp [pow_succ]
      ring
    have h3a : ((3 : ℝ) ^ d) ^ Q = (3 : ℝ) ^ ((d : ℝ) * (Q : ℝ)) := by
      rw [← pow_mul, ← Real.rpow_natCast]
      congr 1
      exact_mod_cast (Nat.cast_mul d Q).symm
    have h3b :
        (3 : ℝ) ^ ((d : ℝ) * (Q : ℝ)) * (3 : ℝ) ^ (-(d : ℝ) * (Q : ℝ) ^ 2) =
          (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1) * (Q : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have h3c : ((3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1))) ^ Q =
          (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1) * (Q : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [h2, mul_pow, mul_pow, h3a]
    rw [h3c]
    rw [← h3b]
    ring
  have hsecond_bound :
      (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
          (3 : ℝ) ^ (-((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ)) ≤
        (1 / 2 : ℝ) * (3 : ℝ) ^ (-12 : ℝ) := by
    calc
      (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
          (3 : ℝ) ^ (-((Q : ℝ) * (d : ℝ) / 2) * (h : ℝ))
          ≤ (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
              (3 : ℝ) ^ (-(d : ℝ) * (Q : ℝ) ^ 2) := hsecond_to_span
      _ = (1 / 2 : ℝ) * (2 * (Q : ℝ) *
            (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1))) ^ Q := hspan_alg
      _ ≤ (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ Q := by
        exact mul_le_mul_of_nonneg_left hA_pow (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ 12 := by
        exact mul_le_mul_of_nonneg_left hthird (by norm_num)
      _ = (1 / 2 : ℝ) * (3 : ℝ) ^ (-12 : ℝ) := by
        norm_num [Real.rpow_neg]
  calc
    (3 : ℝ) ^ (-((1 - γ) / 4) * (h : ℝ)) +
        (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
          (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ))
        ≤ (3 : ℝ) ^ (-6 : ℝ) + (1 / 2 : ℝ) * (3 : ℝ) ^ (-12 : ℝ) := by
          exact add_le_add hfirst (by simpa [hQdef] using hsecond_bound)
    _ < 1 / 8 := by
      norm_num [Real.rpow_neg]

/-- The span-`2Q` coefficient `2^{Q-1}(3^dQ)^Q 3^{-dQ²} ≤ 1/8` used in Step 4, where the
recurrence is applied with the fixed span `2Q` so that the constants do not depend on the
possibly larger `h` (`p.fixed.geometry.one.grid.propagation`). -/
theorem span_coefficient_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
        (3 : ℝ) ^ (-(d : ℝ) * (bigQ d γ : ℝ) ^ 2) ≤ 1 / 8 := by
  let Q : ℕ := Homogenization.HighContrast.bigQ d γ
  have hQ12 : 12 ≤ Q := by
    simpa [Q] using Homogenization.HighContrast.Multiscale.bigQ_twelve_le d hd γ hγ
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num : 0 < 12) hQ12
  have hA_nonneg :
      0 ≤ (2 : ℝ) * (Q : ℝ) *
        (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1)) := by
    positivity
  have hA_le :
      (2 : ℝ) * (Q : ℝ) *
          (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1)) ≤ 1 / 3 := by
    simpa [Q] using
      Homogenization.HighContrast.Multiscale.two_bigQ_mul_three_rpow_le_third d hd γ hγ
  have hA_pow :
      ((2 : ℝ) * (Q : ℝ) *
          (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1))) ^ Q ≤
        (1 / 3 : ℝ) ^ Q := by
    have h := Real.rpow_le_rpow hA_nonneg hA_le (by positivity : 0 ≤ (Q : ℝ))
    simpa [Real.rpow_natCast] using h
  have hthird : (1 / 3 : ℝ) ^ Q ≤ (1 / 3 : ℝ) ^ 12 := by
    rw [one_div_pow, one_div_pow]
    exact one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 3) hQ12
  have hspan_id :
      (2 : ℝ) ^ (Q - 1) * ((3 : ℝ) ^ d * (Q : ℝ)) ^ Q *
          (3 : ℝ) ^ (-(d : ℝ) * (Q : ℝ) ^ 2) =
        (1 / 2 : ℝ) *
          ((2 : ℝ) * (Q : ℝ) *
            (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1))) ^ Q := by
    have htwo : (2 : ℝ) ^ (Q - 1) = (1 / 2 : ℝ) * (2 : ℝ) ^ Q := by
      rw [show Q = (Q - 1) + 1 by omega, pow_succ]
      simp
      ring
    rw [htwo, mul_pow, mul_pow, ← pow_mul]
    rw [← Real.rpow_natCast (3 : ℝ) (d * Q)]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    rw [show (1 / 2 : ℝ) * 2 ^ Q * (3 ^ (↑(d * Q) : ℝ) * ↑Q ^ Q) *
            3 ^ (-(d : ℝ) * ↑Q ^ 2) =
        (1 / 2 : ℝ) * (2 ^ Q * ↑Q ^ Q *
          (3 ^ (↑(d * Q) : ℝ) * 3 ^ (-(d : ℝ) * ↑Q ^ 2))) by ring_nf]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (1 / 2 : ℝ) * ((2 * ↑Q) ^ Q * 3 ^ (-(d : ℝ) * (↑Q - 1) * ↑Q)) =
        (1 / 2 : ℝ) * (2 ^ Q * ↑Q ^ Q * 3 ^ (-(d : ℝ) * (↑Q - 1) * ↑Q)) by
      rw [mul_pow]]
    congr 2
    rw [Nat.cast_mul]
    ring_nf
  calc
    (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
        (3 : ℝ) ^ (-(d : ℝ) * (bigQ d γ : ℝ) ^ 2)
        = (1 / 2 : ℝ) *
          ((2 : ℝ) * (Q : ℝ) *
            (3 : ℝ) ^ (-(d : ℝ) * ((Q : ℝ) - 1))) ^ Q := by
          simpa [Q] using hspan_id
    _ ≤ (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ Q :=
      mul_le_mul_of_nonneg_left hA_pow (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ 12 :=
      mul_le_mul_of_nonneg_left hthird (by norm_num)
    _ ≤ 1 / 8 := by norm_num

/-- `Q·3^{d/2}(1 + (2d)^{1/Q}) ≤ 3^d Q` for `d ≥ 2`, `Q ≥ 2` (`p.fixed.geometry.one.grid.propagation`): the step that
turns the recurrence's printed prefactor into the contraction's. -/
theorem averaging_coefficient_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    (bigQ d γ : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (1 + (2 * (d : ℝ)) ^ ((bigQ d γ : ℝ))⁻¹) ≤
      (3 : ℝ) ^ d * (bigQ d γ : ℝ) := by
  have hQ2 : 2 ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast Homogenization.HighContrast.Multiscale.bigQ_two_le d hd γ hγ
  have hQpos : 0 < (bigQ d γ : ℝ) :=
    Homogenization.HighContrast.Multiscale.bigQ_real_pos d hd γ hγ
  have hd_real : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hsqrt_ind : ∀ n : ℕ, 2 ≤ n → 1 + Real.sqrt (2 * (n:ℝ)) ≤ (3:ℝ) ^ ((n:ℝ)/2) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have e1 : ((2:ℕ):ℝ) = 2 := by norm_num
      have e2 : (2:ℝ) * (2:ℝ) = 4 := by norm_num
      have e3 : (2:ℝ) / 2 = 1 := by norm_num
      have e4 : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [e1, e2, e3, e4, Real.rpow_one]
      norm_num
    | succ n hn ih =>
      have hn_real : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hcast : ((n+1:ℕ):ℝ) = (n:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hpow_eq : (3:ℝ) ^ (((n:ℝ)+1)/2) = (3:ℝ) ^ ((n:ℝ)/2) * Real.sqrt 3 := by
        rw [show ((n:ℝ)+1)/2 = (n:ℝ)/2 + 1/2 by ring,
            Real.rpow_add (by norm_num : (0:ℝ) < 3), ← Real.sqrt_eq_rpow]
      rw [hpow_eq]
      have hsqrt3_ge1 : (1:ℝ) ≤ Real.sqrt 3 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hsqrt_mono : Real.sqrt (2*((n:ℝ)+1)) ≤ Real.sqrt (6*(n:ℝ)) := by
        apply Real.sqrt_le_sqrt
        linarith only [hn_real]
      have hmul : Real.sqrt 3 * Real.sqrt (2*(n:ℝ)) = Real.sqrt (6*(n:ℝ)) := by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
        congr 1
        ring
      have expand : Real.sqrt 3 * (1 + Real.sqrt (2*(n:ℝ))) = Real.sqrt 3 + Real.sqrt (6*(n:ℝ)) := by
        rw [mul_add, mul_one, hmul]
      have key_mul : Real.sqrt 3 * (1 + Real.sqrt (2*(n:ℝ))) ≤ (3:ℝ)^((n:ℝ)/2) * Real.sqrt 3 := by
        rw [mul_comm ((3:ℝ)^((n:ℝ)/2)) (Real.sqrt 3)]
        exact mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg 3)
      rw [expand] at key_mul
      linarith only [hsqrt3_ge1, hsqrt_mono, key_mul]
  have hsqrt_bound : 1 + Real.sqrt (2 * (d:ℝ)) ≤ (3:ℝ) ^ ((d:ℝ)/2) := hsqrt_ind d hd
  have hinv_le : (bigQ d γ : ℝ)⁻¹ ≤ (2:ℝ)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ2
  have h2d_ge1 : (1:ℝ) ≤ 2 * (d:ℝ) := by linarith only [hd_real]
  have step1 : (2 * (d:ℝ)) ^ (bigQ d γ : ℝ)⁻¹ ≤ (2 * (d:ℝ)) ^ (2:ℝ)⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le h2d_ge1 hinv_le
  have step2 : (2 * (d:ℝ)) ^ (2:ℝ)⁻¹ = Real.sqrt (2 * (d:ℝ)) := by
    rw [show (2:ℝ)⁻¹ = 1/2 by norm_num]
    exact (Real.sqrt_eq_rpow (2*(d:ℝ))).symm
  have h1 : (2 * (d:ℝ)) ^ (bigQ d γ : ℝ)⁻¹ ≤ Real.sqrt (2 * (d:ℝ)) := by
    rw [← step2]; exact step1
  have key : (1:ℝ) + (2 * (d:ℝ)) ^ (bigQ d γ : ℝ)⁻¹ ≤ (3:ℝ) ^ ((d:ℝ)/2) := by
    linarith only [h1, hsqrt_bound]
  have h3pos : (0:ℝ) < (3:ℝ) ^ ((d:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hstep : (3:ℝ) ^ ((d:ℝ)/2) * (1 + (2 * (d:ℝ)) ^ (bigQ d γ : ℝ)⁻¹) ≤
      (3:ℝ) ^ ((d:ℝ)/2) * (3:ℝ) ^ ((d:ℝ)/2) :=
    mul_le_mul_of_nonneg_left key (le_of_lt h3pos)
  have hmain : (bigQ d γ : ℝ) * (3:ℝ) ^ ((d:ℝ)/2) * (1 + (2 * (d:ℝ)) ^ (bigQ d γ : ℝ)⁻¹) ≤
      (bigQ d γ : ℝ) * ((3:ℝ) ^ ((d:ℝ)/2) * (3:ℝ) ^ ((d:ℝ)/2)) := by
    calc (bigQ d γ : ℝ) * (3:ℝ) ^ ((d:ℝ)/2) * (1 + (2 * (d:ℝ)) ^ (bigQ d γ : ℝ)⁻¹)
        = (bigQ d γ : ℝ) * ((3:ℝ) ^ ((d:ℝ)/2) * (1 + (2 * (d:ℝ)) ^ (bigQ d γ : ℝ)⁻¹)) := by ring
      _ ≤ (bigQ d γ : ℝ) * ((3:ℝ) ^ ((d:ℝ)/2) * (3:ℝ) ^ ((d:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hQpos)
  have h3sq : (3:ℝ) ^ ((d:ℝ)/2) * (3:ℝ) ^ ((d:ℝ)/2) = (3:ℝ) ^ (d:ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  rw [h3sq] at hmain
  have h3dnat : (3:ℝ) ^ (d:ℝ) = (3:ℝ) ^ d := Real.rpow_natCast 3 d
  rw [h3dnat] at hmain
  have hcomm : (bigQ d γ : ℝ) * (3:ℝ)^d = (3:ℝ)^d * (bigQ d γ : ℝ) := mul_comm _ _
  linarith only [hmain, hcomm]

/-- `e^{(N-1)t}(e^t - 1) ≤ e^{Nt} - 1` for `t ≥ 0` (`p.fixed.geometry.one.grid.propagation`). -/
theorem exp_pred_mul_sub_one_le (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (((N : ℝ) - 1) * t) * (Real.exp t - 1) ≤ Real.exp ((N : ℝ) * t) - 1 := by
  have h1 : 0 ≤ ((N : ℝ) - 1) * t := mul_nonneg (by norm_cast; omega) ht
  have h2 : 1 ≤ Real.exp (((N : ℝ) - 1) * t) := Real.one_le_exp h1
  calc Real.exp (((N : ℝ) - 1) * t) * (Real.exp t - 1)
      = Real.exp (((N : ℝ) - 1) * t) * Real.exp t - Real.exp (((N : ℝ) - 1) * t) := by ring
    _ = Real.exp (((N : ℝ) - 1) * t + t) - Real.exp (((N : ℝ) - 1) * t) := by rw [← Real.exp_add]
    _ = Real.exp ((N : ℝ) * t) - Real.exp (((N : ℝ) - 1) * t) := by ring_nf
    _ ≤ Real.exp ((N : ℝ) * t) - 1 := by linarith only [h2]

/-- `e^x a ≤ a + e^x - 1` for `0 ≤ a ≤ 1` and `x ≥ 0` (`p.fixed.geometry.one.grid.propagation`). -/
theorem exp_mul_le_add_exp_sub_one (x a : ℝ) (hx : 0 ≤ x) (_ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp x * a ≤ a + Real.exp x - 1 := by nlinarith only [Real.one_le_exp hx, ha1]

/-- The geometric tail of the profile weights is bounded by a constant depending only on `γ`
(`p.fixed.geometry.one.grid.propagation`, "the geometric sum is bounded by `C`"). -/
theorem profile_geometric_weight_sum_le (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (a b : ℤ) :
    ∑ j ∈ Finset.Ico a b, (3 : ℝ) ^ (-((1 - γ) / 4) * ((b : ℝ) - 1 - (j : ℝ))) ≤
      (1 - (3 : ℝ) ^ (-((1 - γ) / 4))) ⁻¹ := by
  set r : ℝ := (3 : ℝ) ^ (-((1 - γ) / 4)) with hr_def
  have hr0 : 0 ≤ r := by
    rw [hr_def]; exact Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr_def]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have hγ1 : γ < 1 := hγ.2
    linarith only [hγ1]
  have hsum_eq : ∑ j ∈ Finset.Ico a b, (3 : ℝ) ^ (-((1 - γ) / 4) * ((b : ℝ) - 1 - (j : ℝ)))
      = ∑ k ∈ Finset.range (b - a).toNat, r ^ k := by
    refine Finset.sum_nbij' (fun j => (b - 1 - j).toNat) (fun k => b - 1 - (k : ℤ))
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      show (b - 1 - j).toNat ∈ Finset.range (b - a).toNat
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      show b - 1 - (k : ℤ) ∈ Finset.Ico a b
      simp only [Finset.mem_Ico]
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      show b - 1 - (((b - 1 - j).toNat : ℕ) : ℤ) = j
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      show (b - 1 - (b - 1 - (k : ℤ))).toNat = k
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      have hnn : (0 : ℤ) ≤ b - 1 - j := by omega
      have hcast : (((b - 1 - j).toNat : ℕ) : ℝ) = (b : ℝ) - 1 - (j : ℝ) := by
        have h1 : (((b - 1 - j).toNat : ℕ) : ℤ) = b - 1 - j := Int.toNat_of_nonneg hnn
        have h2 := congrArg (fun x : ℤ => (x : ℝ)) h1
        push_cast at h2
        linarith only [h2]
      show (3 : ℝ) ^ (-((1 - γ) / 4) * ((b : ℝ) - 1 - (j : ℝ))) = r ^ (b - 1 - j).toNat
      rw [hr_def, ← Real.rpow_natCast ((3 : ℝ) ^ (-((1 - γ) / 4))) (b - 1 - j).toNat,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      rw [hcast]
  rw [hsum_eq]
  have hsummable : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hle : ∑ k ∈ Finset.range (b - a).toNat, r ^ k ≤ ∑' k : ℕ, r ^ k :=
    Summable.sum_le_tsum (Finset.range (b - a).toNat) (fun i _ => pow_nonneg hr0 i) hsummable
  rw [tsum_geometric_of_lt_one hr0 hr1] at hle
  exact hle

end

end Homogenization.HighContrast.Multiscale
