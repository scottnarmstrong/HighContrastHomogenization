/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.ChoiceData

/-!
# Amortized hitting for the initial workload

This file isolates the elementary recurrence argument used to find the first
small identity-grid checkpoint.  A contracting workload may be inflated by a
nonnegative determinant charge.  The logarithm of one plus the workload pays
linearly for that charge, while every step above the target makes a fixed
strict decrease.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open scoped ENNReal

noncomputable section

/-! ## One-step logarithmic bounds -/

/-- The affine exponential recurrence is bounded multiplicatively after adding
one. -/
private theorem one_add_recurrence_le {lambda C Q delta x y : ℝ}
    (hlambda0 : 0 ≤ lambda) (hQ : 0 ≤ Q) (hdelta : 0 ≤ delta) (hx : 0 ≤ x)
    (hy : y ≤ lambda * Real.exp (Q * delta) * x +
      C * (Real.exp (Q * delta) - 1)) :
    1 + y ≤ Real.exp (Q * max 1 C * delta) * (1 + lambda * x) := by
  let e : ℝ := Real.exp (Q * delta)
  let Cp : ℝ := max 1 C
  have he1 : 1 ≤ e := by
    dsimp [e]
    exact Real.one_le_exp (mul_nonneg hQ hdelta)
  have hs : -1 ≤ e - 1 := by linarith only [he1]
  have hCp1 : 1 ≤ Cp := by exact le_max_left _ _
  have hCCp : C ≤ Cp := by exact le_max_right _ _
  have hpow : 1 + C * (e - 1) ≤ e ^ Cp := by
    calc
      1 + C * (e - 1) ≤ 1 + Cp * (e - 1) := by
        simpa only [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hCCp (sub_nonneg.mpr he1)) 1
      _ ≤ (1 + (e - 1)) ^ Cp := one_add_mul_self_le_rpow_one_add hs hCp1
      _ = e ^ Cp := by ring_nf
  have he0 : 0 < e := by dsimp [e]; positivity
  have hexp : e ^ Cp = Real.exp (Q * Cp * delta) := by
    rw [Real.rpow_def_of_pos he0]
    dsimp [e]
    rw [Real.log_exp]
    congr 1
    ring
  have hemono : e ≤ Real.exp (Q * Cp * delta) := by
    dsimp [e]
    exact Real.exp_le_exp.mpr <| by
      have hQC : Q ≤ Q * Cp := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hCp1 hQ
      exact mul_le_mul_of_nonneg_right hQC hdelta
  have hlx : 0 ≤ lambda * x := mul_nonneg hlambda0 hx
  calc
    1 + y ≤ e * (lambda * x) + (1 + C * (e - 1)) := by
      dsimp [e]
      linarith only [hy]
    _ ≤ Real.exp (Q * Cp * delta) * (lambda * x) +
        Real.exp (Q * Cp * delta) :=
      add_le_add (mul_le_mul_of_nonneg_right hemono hlx) (hpow.trans_eq hexp)
    _ = Real.exp (Q * max 1 C * delta) * (1 + lambda * x) := by
      dsimp [Cp]
      ring

/-- Above a positive target, the affine exponential recurrence decreases
`log (1 + x)` by a fixed amount after paying linearly for the charge. -/
theorem exists_initialLogAmortization {lambda C Q eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hQ : 0 ≤ Q) (heta : 0 < eta) :
    ∃ A c0 : ℝ, 0 ≤ A ∧ 0 < c0 ∧
      (∀ {delta x y : ℝ}, 0 ≤ delta → 0 ≤ x → 0 ≤ y →
        y ≤ lambda * Real.exp (Q * delta) * x +
          C * (Real.exp (Q * delta) - 1) →
        Real.log (1 + y) ≤ Real.log (1 + x) + A * delta) ∧
      ∀ {delta x y : ℝ}, 0 ≤ delta → 0 ≤ x → 0 ≤ y → eta < x →
        y ≤ lambda * Real.exp (Q * delta) * x +
          C * (Real.exp (Q * delta) - 1) →
        Real.log (1 + y) ≤ Real.log (1 + x) + A * delta - c0 := by
  let A : ℝ := Q * max 1 C
  let theta : ℝ := (1 + lambda * eta) / (1 + eta)
  let c0 : ℝ := -Real.log theta
  have hA : 0 ≤ A := mul_nonneg hQ (le_trans zero_le_one (le_max_left _ _))
  have heta1 : 0 < 1 + eta := by linarith only [heta]
  have hlambda1' : lambda ≤ 1 := hlambda1.le
  have hnum : 0 < 1 + lambda * eta := by
    have := mul_nonneg hlambda0 heta.le
    linarith only [this]
  have htheta0 : 0 < theta := div_pos hnum heta1
  have htheta1 : theta < 1 := by
    rw [div_lt_one heta1]
    have hmul := mul_lt_mul_of_pos_right hlambda1 heta
    linarith only [hmul]
  have hc0 : 0 < c0 := by
    dsimp [c0]
    exact neg_pos.mpr (Real.log_neg htheta0 htheta1)
  have hgrowth : ∀ {delta x y : ℝ}, 0 ≤ delta → 0 ≤ x → 0 ≤ y →
      y ≤ lambda * Real.exp (Q * delta) * x + C * (Real.exp (Q * delta) - 1) →
      Real.log (1 + y) ≤ Real.log (1 + x) + A * delta := by
    intro delta x y hdelta hx hy0 hy
    have honeY : 0 < 1 + y := by linarith only [hy0]
    have honeX : 0 < 1 + x := by linarith only [hx]
    have hstep := one_add_recurrence_le hlambda0 hQ hdelta hx hy
    have hstep' : 1 + y ≤ Real.exp (A * delta) * (1 + x) := by
      refine hstep.trans ?_
      dsimp [A]
      gcongr
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hlambda1' hx
    have hlog := Real.log_le_log honeY hstep'
    rw [Real.log_mul (Real.exp_ne_zero _) honeX.ne', Real.log_exp] at hlog
    simpa only [add_comm] using hlog
  refine ⟨A, c0, hA, hc0, hgrowth, ?_⟩
  intro delta x y hdelta hx hy0 hetax hy
  have honeY : 0 < 1 + y := by linarith only [hy0]
  have honeX : 0 < 1 + x := by linarith only [hx]
  have hmulTheta : 1 + lambda * x ≤ theta * (1 + x) := by
    rw [show theta = (1 + lambda * eta) / (1 + eta) by rfl]
    rw [div_mul_eq_mul_div, le_div_iff₀ heta1]
    have hgap : 0 ≤ (1 - lambda) * (x - eta) :=
      mul_nonneg (sub_nonneg.mpr hlambda1') (sub_nonneg.mpr hetax.le)
    nlinarith only [hgap]
  have hthetaX : 0 < theta * (1 + x) := mul_pos htheta0 honeX
  have hstep := one_add_recurrence_le hlambda0 hQ hdelta hx hy
  have hmain : 1 + y ≤ Real.exp (A * delta) * (theta * (1 + x)) := by
    calc
      1 + y ≤ Real.exp (Q * max 1 C * delta) * (1 + lambda * x) := hstep
      _ ≤ Real.exp (Q * max 1 C * delta) * (theta * (1 + x)) := by gcongr
      _ = Real.exp (A * delta) * (theta * (1 + x)) := by rfl
  have hlog := Real.log_le_log honeY hmain
  rw [Real.log_mul (Real.exp_ne_zero _) hthetaX.ne', Real.log_exp,
    Real.log_mul htheta0.ne' honeX.ne'] at hlog
  dsimp [c0]
  linarith only [hlog]

/-- A polynomial seed has logarithmic size on every base at least three. -/
theorem log_one_add_mul_rpow_le_logb {C p x : ℝ}
    (hC : 0 ≤ C) (hp : 0 ≤ p) (hx : 3 ≤ x) :
    Real.log (1 + C * x ^ p) ≤
      (Real.log (1 + C) + (p + 1) * Real.log 3) * Real.logb 3 x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 3).trans hx
  have hxp1 : 1 ≤ x ^ p := Real.one_le_rpow hx1 hp
  have hCp : 0 ≤ 1 + C := by linarith only [hC]
  have hmain : 1 + C * x ^ p ≤ (1 + C) * x ^ (p + 1) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
    have hfirst : 1 + C * x ^ p ≤ (1 + C) * x ^ p := by
      nlinarith only [hxp1, hC]
    calc
      1 + C * x ^ p ≤ (1 + C) * x ^ p := hfirst
      (1 + C) * x ^ p ≤ ((1 + C) * x ^ p) * x := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hx1 (mul_nonneg hCp (Real.rpow_nonneg hx0.le p))
      _ = (1 + C) * (x ^ p * x) := by ring
  have hleft0 : 0 < 1 + C * x ^ p := by positivity
  have hright0 : 0 < (1 + C) * x ^ (p + 1) := by positivity
  have hlog := Real.log_le_log hleft0 hmain
  rw [Real.log_mul (by positivity : 1 + C ≠ 0) (ne_of_gt (Real.rpow_pos_of_pos hx0 _)),
    Real.log_rpow hx0] at hlog
  have hlogC : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith only [hC])
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogx : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  rw [Real.logb]
  have hratio : Real.log (1 + C) ≤
      Real.log (1 + C) / Real.log 3 * Real.log x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog3]
    exact mul_le_mul_of_nonneg_left hlogx hlogC
  calc
    Real.log (1 + C * x ^ p) ≤ Real.log (1 + C) + (p + 1) * Real.log x := hlog
    _ ≤ Real.log (1 + C) / Real.log 3 * Real.log x +
        (p + 1) * Real.log x := by
          simpa only [add_comm] using add_le_add_right hratio ((p + 1) * Real.log x)
    _ = (Real.log (1 + C) + (p + 1) * Real.log 3) *
        (Real.log x / Real.log 3) := by field_simp

/-- Every scale `R + h` belongs to an `h`-progression seeded between `b + h`
and `b + 2h`. -/
theorem exists_initialAlignment {b R h : ℤ} (hbR : b ≤ R) (hh : 1 ≤ h) :
    ∃ L : ℤ, ∃ m : ℕ, h ≤ L ∧ L < 2 * h ∧ b + L + (m : ℤ) * h = R + h := by
  let a : ℕ := (R - b).toNat
  let hn : ℕ := h.toNat
  have ha : (a : ℤ) = R - b := Int.toNat_of_nonneg (by omega)
  have hhn : (hn : ℤ) = h := Int.toNat_of_nonneg (by omega)
  have hn0 : 0 < hn := Int.natCast_pos.mp <| by rw [hhn]; omega
  let r : ℕ := a % hn
  let m : ℕ := a / hn
  have hr : r < hn := Nat.mod_lt _ hn0
  have hsplit : r + hn * m = a := Nat.mod_add_div a hn
  have hrcast : (r : ℤ) < h := by rw [← hhn]; exact_mod_cast hr
  have hsplitZ : (r : ℤ) + (hn : ℤ) * (m : ℤ) = (a : ℤ) := by exact_mod_cast hsplit
  refine ⟨h + (r : ℤ), m, by omega, by omega, ?_⟩
  rw [hhn, ha] at hsplitZ
  linear_combination hsplitZ

/-- A real span bound and the ceiling window condition place the last point of
an aligned progression inside the integer window. -/
theorem initialProgression_last_le {Tseed R h M : ℤ} {Chit Lam : ℝ} {m K : ℕ}
    (halign : Tseed + (m : ℤ) * h = R + h)
    (hspan : (h : ℝ) + (K : ℝ) * (h : ℝ) ≤ Chit * Lam)
    (hwindow : R + ⌈Chit * Lam⌉ ≤ M) :
    Tseed + ((m + K : ℕ) : ℤ) * h ≤ M := by
  have hreal : ((Tseed + ((m + K : ℕ) : ℤ) * h : ℤ) : ℝ) ≤
      (R : ℝ) + Chit * Lam := by
    have halignR : (Tseed : ℝ) + (m : ℝ) * (h : ℝ) = (R : ℝ) + (h : ℝ) := by
      exact_mod_cast halign
    push_cast
    nlinarith only [halignR, hspan]
  have hceil : (R : ℝ) + Chit * Lam ≤ ((R + ⌈Chit * Lam⌉ : ℤ) : ℝ) := by
    push_cast
    simpa only [add_comm] using add_le_add_left (Int.le_ceil (Chit * Lam)) (R : ℝ)
  have hwindowR : ((R + ⌈Chit * Lam⌉ : ℤ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hwindow
  exact_mod_cast hreal.trans (hceil.trans hwindowR)

/-! ## A finite hitting lemma -/

/-- A nonnegative extended workload satisfying the charged recurrence must hit
the target during any tail longer than its logarithmic budget. -/
theorem exists_initialWork_le_of_budget
    {W : ℕ → ℝ≥0∞} {charge : ℕ → ℝ}
    {lambda C Q eta x0 A c0 D L0 : ℝ} {m K : ℕ}
    (hlambda0 : 0 ≤ lambda)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (heta : 0 < eta)
    (hx0 : 0 ≤ x0) (hW0 : W 0 ≤ ENNReal.ofReal x0)
    (hcharge : ∀ n : ℕ, n < m + K → 0 ≤ charge n)
    (hbudget : ∑ n ∈ Finset.range (m + K), charge n ≤ D)
    (hrec : ∀ n : ℕ, n < m + K →
      W (n + 1) ≤
        ENNReal.ofReal (lambda * Real.exp (Q * charge n)) * W n +
          ENNReal.ofReal (C * (Real.exp (Q * charge n) - 1)))
    (hlog0 : Real.log (1 + x0) ≤ L0)
    (hamort : 0 ≤ A ∧ 0 < c0 ∧
      (∀ {delta x y : ℝ}, 0 ≤ delta → 0 ≤ x → 0 ≤ y →
        y ≤ lambda * Real.exp (Q * delta) * x +
          C * (Real.exp (Q * delta) - 1) →
        Real.log (1 + y) ≤ Real.log (1 + x) + A * delta) ∧
      ∀ {delta x y : ℝ}, 0 ≤ delta → 0 ≤ x → 0 ≤ y → eta < x →
        y ≤ lambda * Real.exp (Q * delta) * x +
          C * (Real.exp (Q * delta) - 1) →
        Real.log (1 + y) ≤ Real.log (1 + x) + A * delta - c0)
    (hlength : L0 + A * D < (K : ℝ) * c0) :
    ∃ n : ℕ, n < K ∧ W (m + n) ≤ ENNReal.ofReal eta := by
  let x : ℕ → ℝ := fun n => Nat.rec x0
    (fun k value => lambda * Real.exp (Q * charge k) * value +
      C * (Real.exp (Q * charge k) - 1)) n
  have hxzero : x 0 = x0 := rfl
  have hxsucc : ∀ n : ℕ, x (n + 1) =
      lambda * Real.exp (Q * charge n) * x n +
        C * (Real.exp (Q * charge n) - 1) := by
    intro n
    rfl
  have hxnonneg : ∀ n : ℕ, n ≤ m + K → 0 ≤ x n := by
    intro n hn
    induction n with
    | zero => simpa only [hxzero] using hx0
    | succ n ih =>
        rw [hxsucc]
        have hnlt : n < m + K := by omega
        have he : 1 ≤ Real.exp (Q * charge n) :=
          Real.one_le_exp (mul_nonneg hQ (hcharge n hnlt))
        exact add_nonneg (mul_nonneg (mul_nonneg hlambda0 (Real.exp_pos _).le) (ih (by omega)))
          (mul_nonneg hC (sub_nonneg.mpr he))
  have hmajor : ∀ n : ℕ, n ≤ m + K → W n ≤ ENNReal.ofReal (x n) := by
    intro n hn
    induction n with
    | zero => simpa only [hxzero] using hW0
    | succ n ih =>
        have hnlt : n < m + K := by omega
        rw [hxsucc]
        refine (hrec n hnlt).trans ?_
        have hcoef0 : 0 ≤ lambda * Real.exp (Q * charge n) := by positivity
        have hadd0 : 0 ≤ C * (Real.exp (Q * charge n) - 1) := by
          exact mul_nonneg hC (sub_nonneg.mpr
            (Real.one_le_exp (mul_nonneg hQ (hcharge n hnlt))))
        rw [ENNReal.ofReal_add (mul_nonneg hcoef0 (hxnonneg n (by omega))) hadd0,
          ENNReal.ofReal_mul hcoef0]
        exact add_le_add (mul_le_mul' le_rfl (ih (by omega))) le_rfl
  by_contra hnone
  push Not at hnone
  have htail : ∀ n : ℕ, n < K → eta < x (m + n) := by
    intro n hn
    have hnot := hnone n hn
    have hmaj := hmajor (m + n) (by omega)
    have hle : ENNReal.ofReal eta < ENNReal.ofReal (x (m + n)) :=
      (hnone n hn).trans_le hmaj
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg heta.le).mp hle
  have hprefix : Real.log (1 + x m) ≤
      Real.log (1 + x0) + A * ∑ n ∈ Finset.range m, charge n := by
    have hp : ∀ r : ℕ, r ≤ m → Real.log (1 + x r) ≤
        Real.log (1 + x0) + A * ∑ n ∈ Finset.range r, charge n := by
      intro r hr
      induction r with
      | zero => simp [hxzero]
      | succ r ih =>
          have hrlt : r < m + K := by omega
          have hlog := hamort.2.2.1 (hcharge r hrlt) (hxnonneg r (by omega))
            (hxnonneg (r + 1) (by omega)) (le_of_eq (hxsucc r).symm)
          rw [Finset.sum_range_succ]
          linarith only [ih (by omega), hlog]
    exact hp m le_rfl
  have htailLog : Real.log (1 + x (m + K)) ≤
      Real.log (1 + x m) + A * ∑ n ∈ Finset.range K, charge (m + n) -
        (K : ℝ) * c0 := by
    have hp : ∀ k : ℕ, k ≤ K → Real.log (1 + x (m + k)) ≤
        Real.log (1 + x m) + A * ∑ n ∈ Finset.range k, charge (m + n) -
          (k : ℝ) * c0 := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
          have hstep := hamort.2.2.2 (hcharge (m + k) (by omega))
            (hxnonneg (m + k) (by omega)) (hxnonneg (m + k + 1) (by omega))
            (htail k (by omega)) (le_of_eq (hxsucc _).symm)
          rw [Finset.sum_range_succ]
          push_cast
          have hi := ih (by omega)
          rw [show m + (k + 1) = m + k + 1 by omega]
          linarith only [hi, hstep]
    exact hp K le_rfl
  have hsumSplit : ∑ n ∈ Finset.range (m + K), charge n =
      (∑ n ∈ Finset.range m, charge n) +
        ∑ n ∈ Finset.range K, charge (m + n) := by
    simpa only [add_comm] using Finset.sum_range_add charge m K
  have hfinal : Real.log (1 + x (m + K)) ≤ L0 + A * D - (K : ℝ) * c0 := by
    have hA := hamort.1
    rw [hsumSplit] at hbudget
    calc
      Real.log (1 + x (m + K)) ≤
          Real.log (1 + x m) + A * ∑ n ∈ Finset.range K, charge (m + n) -
            (K : ℝ) * c0 := htailLog
      _ ≤ (Real.log (1 + x0) + A * ∑ n ∈ Finset.range m, charge n) +
          A * ∑ n ∈ Finset.range K, charge (m + n) - (K : ℝ) * c0 := by
            linarith only [hprefix]
      _ ≤ L0 + A * D - (K : ℝ) * c0 := by
        have hmul := mul_le_mul_of_nonneg_left hbudget hA
        linarith only [hlog0, hmul]
  have hlognonneg : 0 ≤ Real.log (1 + x (m + K)) :=
    Real.log_nonneg (by linarith only [hxnonneg (m + K) (by omega)])
  linarith only [hfinal, hlognonneg, hlength]

end

end Selection
end HighContrast
end Homogenization
