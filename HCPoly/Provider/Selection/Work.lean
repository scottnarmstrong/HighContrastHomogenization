/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.State

/-!
# Scalar work estimates for the global selector

The logarithmic profile work is scaled by its readiness threshold.  The
resulting scalar function has a service slope independent of that threshold,
and a strict contraction whenever the incoming profile is above threshold.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

/-- The scaled logarithmic work `Φ_η(y)`. -/
def scaledWork (eta y : ℝ) : ℝ :=
  eta * Real.log (1 + eta⁻¹ * y)

/-- Defining equation for the scaled logarithmic work. -/
theorem scaledWork_eq (eta y : ℝ) :
    scaledWork eta y = eta * Real.log (1 + eta⁻¹ * y) := rfl

/-- The charge accumulated by all length-`h` service intervals ending at a
fixed cursor. -/
def serviceWindowCharge {d : ℕ} (P : MeasureTheory.Measure (CoeffSpace d))
    (q : Mat d) (h u : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc (u + 1) (u + h), detLoss P q (j - h) j

/-- Defining equation for the service-window charge. -/
theorem serviceWindowCharge_eq {d : ℕ}
    (P : MeasureTheory.Measure (CoeffSpace d)) (q : Mat d) (h u : ℤ) :
    serviceWindowCharge P q h u =
      ∑ j ∈ Finset.Icc (u + 1) (u + h), detLoss P q (j - h) j := rfl

/-- The strict work decrement created by a profile contraction. -/
def workDecrement (lambda : ℝ) : ℝ :=
  Real.log (2 / (1 + lambda))

/-- Defining equation for the strict work decrement. -/
theorem workDecrement_eq (lambda : ℝ) :
    workDecrement lambda = Real.log (2 / (1 + lambda)) := rfl

/-- The additive work load of a fixed-span propagation estimate. -/
def fixedSpanLoad (A : ℝ) : ℝ :=
  Real.log (1 + 2 * A)

/-- Defining equation for the fixed-span load. -/
theorem fixedSpanLoad_eq (A : ℝ) :
    fixedSpanLoad A = Real.log (1 + 2 * A) := rfl

/-- Scaling a logarithm by a threshold at most one cannot increase the
unscaled logarithm with the same numerator. -/
theorem scaled_log_one_add_div_le {eta C : ℝ} (heta : 0 < eta)
    (hetaOne : eta ≤ 1) (hC : 0 ≤ C) :
    eta * Real.log (1 + C / eta) ≤ Real.log (1 + C) := by
  have hratio : 0 ≤ C / eta := div_nonneg hC heta.le
  have hpow := rpow_one_add_le_one_add_mul_self
    (s := C / eta) (by linarith only [hratio]) heta.le hetaOne
  have hpow' : (1 + C / eta) ^ eta ≤ 1 + C := by
    convert hpow using 1
    field_simp
  have hbase : 0 < 1 + C / eta := by positivity
  have hright : 0 < 1 + C := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Real.rpow_pos_of_pos hbase eta) hright hpow'
  rw [Real.log_rpow hbase] at hlog
  exact hlog

/-- The decrement constant is positive for a strict contraction factor. -/
theorem workDecrement_pos {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hlambdaOne : lambda < 1) :
    0 < workDecrement lambda := by
  rw [workDecrement_eq]
  apply Real.log_pos
  rw [lt_div_iff₀ (by linarith only [hlambda])]
  linarith only [hlambdaOne]

/-- Scaled work is monotone in its nonnegative profile coordinate. -/
theorem scaledWork_mono {eta x y : ℝ} (heta : 0 < eta)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    scaledWork eta x ≤ scaledWork eta y := by
  rw [scaledWork_eq, scaledWork_eq]
  apply mul_le_mul_of_nonneg_left _ heta.le
  apply Real.strictMonoOn_log.monotoneOn
  · show 0 < 1 + eta⁻¹ * x
    positivity
  · have hy : 0 ≤ y := hx.trans hxy
    show 0 < 1 + eta⁻¹ * y
    positivity
  · gcongr

/-- A contraction above threshold produces the fixed strict work decrement. -/
theorem scaledWork_contraction {eta lambda p : ℝ} (heta : 0 < eta)
    (hlambda : 0 ≤ lambda) (hlambdaOne : lambda < 1) (hp : eta < p) :
    scaledWork eta (lambda * p) ≤
      scaledWork eta p - eta * workDecrement lambda := by
  have hp0 : 0 < p := heta.trans hp
  have hden : 0 < 1 + eta⁻¹ * p := by positivity
  have hnum : 0 < 1 + eta⁻¹ * (lambda * p) := by positivity
  have hlambdaDen : 0 < 1 + lambda := by linarith only [hlambda]
  have hratio :
      (1 + eta⁻¹ * (lambda * p)) / (1 + eta⁻¹ * p) ≤
        (1 + lambda) / 2 := by
    rw [div_le_iff₀ hden]
    field_simp
    have hprod : 0 ≤ (1 - lambda) * (p - eta) :=
      mul_nonneg (by linarith only [hlambdaOne]) (sub_nonneg.mpr hp.le)
    nlinarith only [hprod]
  have hratioPos : 0 <
      (1 + eta⁻¹ * (lambda * p)) / (1 + eta⁻¹ * p) := div_pos hnum hden
  have hhalfPos : 0 < (1 + lambda) / 2 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hratioPos hhalfPos hratio
  have hlogDiv :
      Real.log ((1 + eta⁻¹ * (lambda * p)) / (1 + eta⁻¹ * p)) =
        Real.log (1 + eta⁻¹ * (lambda * p)) -
          Real.log (1 + eta⁻¹ * p) := by
    rw [Real.log_div hnum.ne' hden.ne']
  have hhalf : (1 + lambda) / 2 = (2 / (1 + lambda))⁻¹ := by
    field_simp
  rw [hlogDiv, hhalf, Real.log_inv, ← workDecrement_eq] at hlog
  rw [scaledWork_eq, scaledWork_eq]
  have hm := mul_le_mul_of_nonneg_left hlog heta.le
  nlinarith only [hm]

/-- A fixed-span propagation bound gives an additive work load whose
determinant slope is one. -/
theorem scaledWork_fixedSpan {eta A p p' x : ℝ} (heta : 0 < eta)
    (hetaOne : eta ≤ 1) (hA : 0 ≤ A) (hpOne : p ≤ 1)
    (hp' : 0 ≤ p') (hx : 0 ≤ x)
    (hprop : p' ≤ A * p + A * (Real.exp x - 1)) :
    scaledWork eta p' ≤ fixedSpanLoad A + x := by
  have hexp : 1 ≤ Real.exp x := (Real.exp_zero ▸ Real.exp_le_exp.mpr hx)
  have hpA : A * p ≤ A := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpOne hA
  have hp'exp : p' ≤ A * Real.exp x := by
    nlinarith only [hprop, hpA]
  have hfirst :
      1 + eta⁻¹ * p' ≤ 1 + eta⁻¹ * (A * Real.exp x) := by
    gcongr
  have hreassoc : eta⁻¹ * (A * Real.exp x) = Real.exp x * (A / eta) := by
    field_simp
  have hmiddle :
      1 + eta⁻¹ * (A * Real.exp x) ≤
        Real.exp x * (1 + A / eta) := by
    rw [hreassoc]
    nlinarith only [hexp]
  have hdiv : A / eta ≤ 2 * A / eta := by
    exact div_le_div_of_nonneg_right (by linarith only [hA]) heta.le
  have hlast : Real.exp x * (1 + A / eta) ≤
      Real.exp x * (1 + 2 * A / eta) := by
    gcongr
  have harg := hfirst.trans (hmiddle.trans hlast)
  have hleft : 0 < 1 + eta⁻¹ * p' := by positivity
  have hfactor : 0 < 1 + 2 * A / eta := by positivity
  have hright : 0 < Real.exp x * (1 + 2 * A / eta) := mul_pos (Real.exp_pos x) hfactor
  have hlog := Real.strictMonoOn_log.monotoneOn hleft hright harg
  have hscaledLog := scaled_log_one_add_div_le (C := 2 * A) heta hetaOne
    (mul_nonneg (by norm_num) hA)
  have hetaX : eta * x ≤ x := by
    nlinarith only [hetaOne, hx, mul_nonneg heta.le hx]
  rw [scaledWork_eq]
  calc
    eta * Real.log (1 + eta⁻¹ * p')
        ≤ eta * Real.log (Real.exp x * (1 + 2 * A / eta)) :=
      mul_le_mul_of_nonneg_left hlog heta.le
    _ = eta * x + eta * Real.log (1 + 2 * A / eta) := by
      rw [Real.log_mul (Real.exp_ne_zero x) hfactor.ne', Real.log_exp]
      ring
    _ ≤ x + Real.log (1 + 2 * A) := add_le_add hetaX hscaledLog
    _ = fixedSpanLoad A + x := by rw [fixedSpanLoad_eq]; ring

/-- Portable service above the contracted input increases scaled work by at
most a uniform multiple of the exponential charge. -/
theorem scaledWork_service_from_contraction {eta lambda C p p' X : ℝ}
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hlambda : 0 ≤ lambda)
    (hC : 0 ≤ C) (hp : 0 ≤ p) (hp' : 0 ≤ p') (hX : 0 ≤ X)
    (hservice : p' ≤ lambda * Real.exp X * p + C * (Real.exp X - 1)) :
    scaledWork eta p' ≤ scaledWork eta (lambda * p) + max 1 C * X := by
  let curve : ℝ → ℝ := fun x =>
    lambda * Real.exp x * p + C * (Real.exp x - 1)
  let f : ℝ → ℝ := fun x => scaledWork eta (curve x)
  have hcurve0 : ∀ x ∈ Set.Icc (0 : ℝ) X, 0 ≤ curve x := by
    intro x hx
    dsimp [curve]
    have hexp : 1 ≤ Real.exp x := Real.exp_zero ▸ Real.exp_le_exp.mpr hx.1
    exact add_nonneg (by positivity) (mul_nonneg hC (sub_nonneg.mpr hexp))
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) X,
      HasDerivAt f
        (eta * Real.exp x * (lambda * p + C) /
          (eta + lambda * Real.exp x * p + C * (Real.exp x - 1))) x := by
    intro x hx
    have harg : 0 < 1 + eta⁻¹ * curve x := by
      have := hcurve0 x hx
      positivity
    have hinner : HasDerivAt
        (fun y : ℝ => 1 + eta⁻¹ *
          (lambda * Real.exp y * p + C * (Real.exp y - 1)))
        (eta⁻¹ * (Real.exp x * (lambda * p + C))) x := by
      have hfirst := ((Real.hasDerivAt_exp x).const_mul lambda).mul_const p
      have hsecond := ((Real.hasDerivAt_exp x).sub_const 1).const_mul C
      have hsum := hfirst.add hsecond
      have hscale := hsum.const_mul eta⁻¹
      have hplus := hscale.const_add 1
      convert hplus using 1 <;> first | rfl | ring
    have hlog := (hinner.log harg.ne').const_mul eta
    dsimp [f, curve, scaledWork]
    convert hlog using 1 <;> first | rfl | (field_simp; ring)
  have hdiff : DifferentiableOn ℝ f (Set.Icc (0 : ℝ) X) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hslope : ∀ x ∈ interior (Set.Icc (0 : ℝ) X),
      deriv f x ≤ max 1 C := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) X := interior_subset hx
    rw [(hderiv x hx').deriv]
    have hexp : 1 ≤ Real.exp x := Real.exp_zero ▸ Real.exp_le_exp.mpr hx'.1
    have hz : 0 ≤ Real.exp x - 1 := sub_nonneg.mpr hexp
    have hphiOne : 1 ≤ max 1 C := le_max_left _ _
    have hphiC : C ≤ max 1 C := le_max_right _ _
    have hetaPhi : eta ≤ max 1 C := hetaOne.trans hphiOne
    have hden : 0 < eta + lambda * Real.exp x * p + C * (Real.exp x - 1) := by
      have hterm1 : 0 ≤ lambda * Real.exp x * p := by positivity
      have hterm2 : 0 ≤ C * (Real.exp x - 1) := mul_nonneg hC hz
      linarith only [heta, hterm1, hterm2]
    rw [div_le_iff₀ hden]
    have hprofile : eta * Real.exp x * (lambda * p) ≤
        max 1 C * Real.exp x * (lambda * p) := by
      gcongr
    have hconstant : eta * C ≤ max 1 C * eta := by
      nlinarith only [hphiC, heta.le, mul_le_mul_of_nonneg_left hphiC heta.le]
    have hincrement : eta * C * (Real.exp x - 1) ≤
        max 1 C * C * (Real.exp x - 1) := by
      gcongr
    nlinarith only [hprofile, hconstant, hincrement]
  have hmv := (convex_Icc (0 : ℝ) X).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuousOn (hdiff.mono interior_subset) hslope 0
    (Set.left_mem_Icc.mpr hX) X (Set.right_mem_Icc.mpr hX) hX
  have hfzero : f 0 = scaledWork eta (lambda * p) := by
    simp [f, curve]
  have hmono : scaledWork eta p' ≤ f X := by
    dsimp [f]
    apply scaledWork_mono heta hp'
    simpa only [curve] using hservice
  rw [hfzero] at hmv
  nlinarith only [hmono, hmv]

/-- Portable service increases scaled work by at most a uniform multiple of
the exponential charge. -/
theorem scaledWork_service {eta lambda C p p' X : ℝ} (heta : 0 < eta)
    (hetaOne : eta ≤ 1) (hlambda : 0 ≤ lambda) (hlambdaOne : lambda ≤ 1)
    (hC : 0 ≤ C) (hp : 0 ≤ p) (hp' : 0 ≤ p') (hX : 0 ≤ X)
    (hservice : p' ≤ lambda * Real.exp X * p + C * (Real.exp X - 1)) :
    scaledWork eta p' ≤ scaledWork eta p + max 1 C * X := by
  have hstep := scaledWork_service_from_contraction heta hetaOne hlambda hC hp
    hp' hX hservice
  have hcontract : scaledWork eta (lambda * p) ≤ scaledWork eta p := by
    apply scaledWork_mono heta
    · positivity
    · exact mul_le_of_le_one_left hp hlambdaOne
  linarith only [hstep, hcontract]

/-- Above the readiness threshold, portable service includes the fixed strict
work decrement. -/
theorem scaledWork_service_decrement {eta lambda C p p' X : ℝ}
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hlambda : 0 ≤ lambda)
    (hlambdaOne : lambda < 1) (hC : 0 ≤ C) (hp' : 0 ≤ p') (hX : 0 ≤ X)
    (hp : eta < p)
    (hservice : p' ≤ lambda * Real.exp X * p + C * (Real.exp X - 1)) :
    scaledWork eta p' ≤ scaledWork eta p - eta * workDecrement lambda +
      max 1 C * X := by
  have hp0 : 0 ≤ p := (heta.trans hp).le
  have hstep := scaledWork_service_from_contraction heta hetaOne hlambda hC hp0
    hp' hX hservice
  have hcontract := scaledWork_contraction heta hlambda hlambdaOne hp
  linarith only [hstep, hcontract]

end

end Selection
end HighContrast
end Homogenization
