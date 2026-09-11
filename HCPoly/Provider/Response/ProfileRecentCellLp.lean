/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentCellSum
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The probabilistic recent-cell bound

The centered maximum has exactly the terminal centered history as its
`Q`-moment.  Monotonicity of probability-space `L^p` seminorms then turns the
pointwise recent-cell estimate into its printed `L²` bound.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The centered terminal maximum is an a.e. measurable statistic. -/
theorem aemeasurable_profileCenteredMaximum
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {rhoMax : ℝ} {jStar t : ℤ}
    (hEt : BlockPosDef (adaptedMean P q t)) :
    AEMeasurable (profileCenteredMaximum P rhoMax q jStar t) P := by
  have hEts : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  simpa only [profileCenteredMaximum] using
    PortableHistory.aemeasurable_adaptedSup hq hEts hEt
      (fun k ↦ (3 : ℝ) ^ (-rhoMax * ((t : ℝ) - (k : ℝ))))
      jStar t (adaptedCell q t)

/-- The `L^Q` seminorm of the centered maximum is the `Q`-th root of its
defining history. -/
theorem eLpNorm_profileCenteredMaximum_eq
    {P : Measure (CoeffSpace d)} {q : Mat d} {rhoMax Q : ℝ}
    (hQ : 0 < Q) (jStar t : ℤ) :
    eLpNorm (profileCenteredMaximum P rhoMax q jStar t)
        (ENNReal.ofReal Q) P =
      centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ := by
  have hp0 : ENNReal.ofReal Q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hQ
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hQ.le, one_div]
  simp only [enorm_eq_self]
  rfl

/-- On a probability space the centered maximum has `L²` seminorm at most
the `Q`-th root of the centered history. -/
theorem eLpNorm_two_profileCenteredMaximum_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef)
    {rhoMax Q : ℝ} (hQ : 2 ≤ Q) {jStar t : ℤ}
    (hEt : BlockPosDef (adaptedMean P q t)) :
    eLpNorm (profileCenteredMaximum P rhoMax q jStar t) 2 P ≤
      centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ := by
  have hmeas : AEStronglyMeasurable
      (profileCenteredMaximum P rhoMax q jStar t) P :=
    (aemeasurable_profileCenteredMaximum (rhoMax := rhoMax) (jStar := jStar)
      hq hEt).aestronglyMeasurable
  have hpq : (2 : ℝ≥0∞) ≤ ENNReal.ofReal Q := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal hQ
  exact (eLpNorm_le_eLpNorm_of_exponent_le hpq hmeas).trans_eq
    (eLpNorm_profileCenteredMaximum_eq (by linarith only [hQ]) jStar t)

/-- Multiplication by a finite nonnegative scalar costs at most that scalar in
an extended-real `L^p` seminorm. -/
theorem eLpNorm_ofReal_mul_le {X : CoeffSpace d → ℝ≥0∞}
    {P : Measure (CoeffSpace d)} (hX : AEStronglyMeasurable X P)
    (c : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ ENNReal.ofReal c * X x) p P ≤
      ENNReal.ofReal c * eLpNorm X p P := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p hX
  filter_upwards [] with x
  simp only [enorm_eq_self]
  exact le_rfl

/-- The exact recent-cell estimate in `L²`. -/
theorem eLpNorm_diagonalWeakCellSum_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} {H : ℕ}
    {Q alpha rhoMax : ℝ} (hQ : 2 ≤ Q) (hrho : 0 ≤ rhoMax)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ))
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k)) :
    eLpNorm
        (fun coeff ↦ diagonalWeakCellSum q t H (1 / 2)
          (adaptedMean P q t) coeff) 2 P ≤
      ENNReal.ofReal (centeredWindowCoefficient H rhoMax) *
          centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ +
        ENNReal.ofReal (nonlinearCellWindowCoefficient H alpha Q) *
          nonlinearHistory P Q alpha q jStar t ^ Q⁻¹ := by
  let U : CoeffSpace d → ℝ := fun coeff ↦
    diagonalWeakCellSum q t H (1 / 2) (adaptedMean P q t) coeff
  let Z : CoeffSpace d → ℝ≥0∞ := profileCenteredMaximum P rhoMax q jStar t
  let hnl : ℝ≥0∞ := nonlinearHistory P Q alpha q jStar t ^ Q⁻¹
  let ccen : ℝ := centeredWindowCoefficient H rhoMax
  let cnl : ℝ := nonlinearCellWindowCoefficient H alpha Q
  have hU0 : ∀ coeff, 0 ≤ U coeff := fun coeff ↦
    diagonalWeakCellSum_nonneg q t H (1 / 2) (adaptedMean P q t) coeff
  have hZmeas : AEStronglyMeasurable Z P :=
    (aemeasurable_profileCenteredMaximum hq hEt).aestronglyMeasurable
  have hfirstMeas : AEStronglyMeasurable
      (fun coeff ↦ ENNReal.ofReal ccen * Z coeff) P := by
    have hcmeas : AEMeasurable
        (fun _ : CoeffSpace d ↦ ENNReal.ofReal ccen) P := aemeasurable_const
    exact (hcmeas.mul (aemeasurable_profileCenteredMaximum hq hEt)).aestronglyMeasurable
  have hsecondMeas : AEStronglyMeasurable
      (fun _ : CoeffSpace d ↦ ENNReal.ofReal cnl * hnl) P :=
    aestronglyMeasurable_const
  have hpoint : ∀ coeff, ENNReal.ofReal (U coeff) ≤
      ENNReal.ofReal ccen * Z coeff + ENNReal.ofReal cnl * hnl := by
    intro coeff
    exact ofReal_diagonalWeakCellSum_le_profile hq
      (by linarith only [hQ]) hrho hP hgrid hlj hfin hstart hEt hmean coeff
  have hmono : eLpNorm (ENNReal.ofReal ∘ U) 2 P ≤
      eLpNorm
        ((fun coeff ↦ ENNReal.ofReal ccen * Z coeff) +
          fun _ ↦ ENNReal.ofReal cnl * hnl) 2 P := by
    refine eLpNorm_mono_enorm ?_
    intro coeff
    simpa only [Function.comp_apply, Pi.add_apply, enorm_eq_self] using hpoint coeff
  have htriangle := eLpNorm_add_le hfirstMeas hsecondMeas
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfirst : eLpNorm (fun coeff ↦ ENNReal.ofReal ccen * Z coeff) 2 P ≤
      ENNReal.ofReal ccen * centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ :=
    (eLpNorm_ofReal_mul_le hZmeas ccen 2).trans
      (mul_right_mono (eLpNorm_two_profileCenteredMaximum_le hq hQ hEt))
  have hsecond : eLpNorm
      (fun _ : CoeffSpace d ↦ ENNReal.ofReal cnl * hnl) 2 P ≤
      ENNReal.ofReal cnl * hnl := by
    rw [eLpNorm_const _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (IsProbabilityMeasure.ne_zero P), measure_univ, ENNReal.one_rpow, mul_one,
      enorm_eq_self]
  rw [← eLpNorm_ofReal U (Filter.Eventually.of_forall hU0)]
  exact hmono.trans (htriangle.trans (add_le_add hfirst hsecond))

end

end Homogenization.HighContrast.Response
