/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.DeterminantDrift
import HCPoly.Provider.ShortHop.WindowGuard

/-!
# The two drift envelopes of the short test

The successful short test of `p.successful.short.bridge` reads the
fixed-grid determinant drift twice on the old grid, once at the intermediate
scale and once at the terminal scale, and concludes that the drift there is
below the two envelopes `d_n` and `d_t` of the ordered choice.

Both readings are the same three steps.  The window makes the annealed blocks of
the old grid positive definite and ordered on exactly the scales read, so the
determinant drift applies and the drift at the entry scale is nonnegative.  The
short test bounds the determinant root at the entry scale by `1 + δ_short` times
the one at the terminal scale, and the mean order carries that bound to the
intermediate scale as well, so the determinant quotient — the loss `e^{dσ}` of
the propagation — is at most `(1 + δ_short)^d` at both endpoints.  The drift test
bounds the drift at the entry scale by `η_pre`.  Substituting the two bounds into
the propagation gives the envelopes, whose geometric factors are `3^{-ρ_dr ℓ₀}`
and `3^{-2ρ_dr ℓ₀}` because the two endpoints sit one and two hop lengths above
the entry scale.

These are the last two hypotheses of `shortHop_conclusion` that belong to a
neighbouring result.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The determinant quotient under the short test -/

/-- **The determinant quotient is below the determinant tolerance.**  For a pair
of positive definite doubled blocks whose determinant roots the short test
compares, the quotient of the determinants is at most `(1 + δ_short)^d`. -/
theorem det_div_le_of_short_test (hd : d ≠ 0) {Eu En : BlockMat d}
    (hEu : (toFullBlockMat Eu).PosDef) (hEn : (toFullBlockMat En).PosDef) {delta : ℝ}
    (htest : detRoot d Eu ≤ (1 + delta) * detRoot d En) :
    (toFullBlockMat Eu).det / (toFullBlockMat En).det ≤ (1 + delta) ^ d := by
  have hEnroot : 0 < detRoot d En := detRoot_pos hEn
  have hratio : detRoot d Eu / detRoot d En ≤ 1 + delta := (div_le_iff₀ hEnroot).mpr htest
  have hnn : 0 ≤ detRoot d Eu / detRoot d En :=
    div_nonneg (detRoot_pos hEu).le hEnroot.le
  rw [← detRoot_div_pow hd hEu hEn]
  exact pow_le_pow_left₀ hnn hratio d

/-! ## The two envelopes -/

/-- **The drift at the intermediate scale is below the new-scale envelope**
(the first reading of `e.fixed.geometry.drift.advance` in the short
test). -/
theorem linearDrift_le_shortDriftNew [NeZero d] (hd : d ≠ 0) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd Qexp : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Qexp K jStar M) {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {mu : Mat d} (hmu : mu.PosDef)
    {u l0 : ℤ} (hju : jStar ≤ u) (hl0 : 0 ≤ l0)
    (hcont : ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * l0 →
      adaptedCell (roundedGrid jStar mu) j ⊆ centeredCube d M)
    {rhoDr etaPre deltaShort : ℝ} (hrho : 0 ≤ rhoDr) (hdelta : 0 ≤ deltaShort)
    (hpre : linearDrift P rhoDr (roundedGrid jStar mu) jStar u ≤ etaPre)
    (hdet : adaptedDetRoot P (roundedGrid jStar mu) u ≤
      (1 + deltaShort) * adaptedDetRoot P (roundedGrid jStar mu) (u + 2 * l0)) :
    linearDrift P rhoDr (roundedGrid jStar mu) jStar (u + l0) ≤
      shortDriftNew d rhoDr l0 etaPre deltaShort := by
  have hpos : ∀ j : ℤ, jStar ≤ j → j ≤ u + l0 →
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) j)).PosDef := fun j hj hjv =>
    posDef_adaptedMean_of_window hw hY hmu hj (by omega) hcont
  have hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ u + l0 →
      toFullBlockMat (adaptedMean P (roundedGrid jStar mu) t) ≤
        toFullBlockMat (adaptedMean P (roundedGrid jStar mu) s) := fun s t hs hst htv =>
    adaptedMean_le_of_window hstat hw hY hmu hs hst (by omega) hcont
  have hprop := linearDrift_propagation (u := u) (v := u + l0) hrho hju (by omega) hpos hmono
  -- the determinant quotient at the intermediate scale
  have hdetN := detRoot_le_of_short_test
    (posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + l0) (by omega) hcont)
    (posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + 2 * l0) le_rfl hcont)
    (adaptedMean_le_of_window hstat hw hY hmu (by omega : jStar ≤ u + l0) (by omega) le_rfl hcont)
    hdelta hdet
  have hquot := det_div_le_of_short_test (Eu := adaptedMean P (roundedGrid jStar mu) u)
    (En := adaptedMean P (roundedGrid jStar mu) (u + l0)) hd
    (posDef_adaptedMean_of_window hw hY hmu hju (by omega) hcont)
    (posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + l0) (by omega) hcont)
    hdetN
  -- the drift at the entry scale
  have hpre0 := linearDrift_nonneg_of_window (rhoDr := rhoDr) hstat hw hY hmu hju
    (by omega : u ≤ u + 2 * l0) hcont
  have hquot0 : (0 : ℝ) ≤
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) u)).det /
        (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) (u + l0))).det :=
    (div_pos (posDef_adaptedMean_of_window hw hY hmu hju (by omega) hcont).det_pos
      (posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + l0)
        (by omega) hcont).det_pos).le
  -- the geometric factor
  have hexp : ((u + l0 : ℤ) : ℝ) - (u : ℝ) = (l0 : ℝ) := by push_cast; ring
  rw [hexp] at hprop
  have hw3 : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) := by positivity
  have hfirst :
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) u)).det /
            (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) (u + l0))).det *
          (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) *
          linearDrift P rhoDr (roundedGrid jStar mu) jStar u ≤
        (1 + deltaShort) ^ d * (3 : ℝ) ^ (-rhoDr * (l0 : ℝ)) * etaPre :=
    mul_le_mul (mul_le_mul_of_nonneg_right hquot hw3.le) hpre hpre0
      (mul_nonneg (le_trans hquot0 hquot) hw3.le)
  have hsecond : 2 * (d : ℝ) *
      ((toFullBlockMat (adaptedMean P (roundedGrid jStar mu) u)).det /
        (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) (u + l0))).det - 1) ≤
      2 * (d : ℝ) * ((1 + deltaShort) ^ d - 1) := by
    have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith only [hquot]) h2d
  rw [shortDriftNew]
  linarith only [hprop, hfirst, hsecond]

/-- **The drift at the terminal scale is below the terminal-scale envelope**
(the second reading of `e.fixed.geometry.drift.advance` in the short
test). -/
theorem linearDrift_le_shortDriftTerm [NeZero d] (hd : d ≠ 0) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd Qexp : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Qexp K jStar M) {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {mu : Mat d} (hmu : mu.PosDef)
    {u l0 : ℤ} (hju : jStar ≤ u) (hl0 : 0 ≤ l0)
    (hcont : ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * l0 →
      adaptedCell (roundedGrid jStar mu) j ⊆ centeredCube d M)
    {rhoDr etaPre deltaShort : ℝ} (hrho : 0 ≤ rhoDr)
    (hpre : linearDrift P rhoDr (roundedGrid jStar mu) jStar u ≤ etaPre)
    (hdet : adaptedDetRoot P (roundedGrid jStar mu) u ≤
      (1 + deltaShort) * adaptedDetRoot P (roundedGrid jStar mu) (u + 2 * l0)) :
    linearDrift P rhoDr (roundedGrid jStar mu) jStar (u + 2 * l0) ≤
      shortDriftTerm d rhoDr l0 etaPre deltaShort := by
  have hpos : ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * l0 →
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) j)).PosDef := fun j hj hjv =>
    posDef_adaptedMean_of_window hw hY hmu hj hjv hcont
  have hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ u + 2 * l0 →
      toFullBlockMat (adaptedMean P (roundedGrid jStar mu) t) ≤
        toFullBlockMat (adaptedMean P (roundedGrid jStar mu) s) := fun s t hs hst htv =>
    adaptedMean_le_of_window hstat hw hY hmu hs hst htv hcont
  have hprop := linearDrift_propagation (u := u) (v := u + 2 * l0) hrho hju (by omega) hpos hmono
  have hquot := det_div_le_of_short_test (Eu := adaptedMean P (roundedGrid jStar mu) u)
    (En := adaptedMean P (roundedGrid jStar mu) (u + 2 * l0)) hd
    (posDef_adaptedMean_of_window hw hY hmu hju (by omega) hcont)
    (posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + 2 * l0) le_rfl hcont)
    hdet
  have hpre0 := linearDrift_nonneg_of_window (rhoDr := rhoDr) hstat hw hY hmu hju
    (by omega : u ≤ u + 2 * l0) hcont
  have hquot0 : (0 : ℝ) ≤
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) u)).det /
        (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0))).det :=
    (div_pos (posDef_adaptedMean_of_window hw hY hmu hju (by omega) hcont).det_pos
      (posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + 2 * l0)
        le_rfl hcont).det_pos).le
  have hexp : -rhoDr * (((u + 2 * l0 : ℤ) : ℝ) - (u : ℝ)) = -2 * rhoDr * (l0 : ℝ) := by
    push_cast; ring
  rw [hexp] at hprop
  have hw3 : (0 : ℝ) < (3 : ℝ) ^ (-2 * rhoDr * (l0 : ℝ)) := by positivity
  have hfirst :
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) u)).det /
            (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0))).det *
          (3 : ℝ) ^ (-2 * rhoDr * (l0 : ℝ)) *
          linearDrift P rhoDr (roundedGrid jStar mu) jStar u ≤
        (1 + deltaShort) ^ d * (3 : ℝ) ^ (-2 * rhoDr * (l0 : ℝ)) * etaPre :=
    mul_le_mul (mul_le_mul_of_nonneg_right hquot hw3.le) hpre hpre0
      (mul_nonneg (le_trans hquot0 hquot) hw3.le)
  have hsecond : 2 * (d : ℝ) *
      ((toFullBlockMat (adaptedMean P (roundedGrid jStar mu) u)).det /
        (toFullBlockMat (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0))).det - 1) ≤
      2 * (d : ℝ) * ((1 + deltaShort) ^ d - 1) := by
    have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith only [hquot]) h2d
  rw [shortDriftTerm]
  linarith only [hprop, hfirst, hsecond]

end

end ShortHop
end HighContrast
end Homogenization
