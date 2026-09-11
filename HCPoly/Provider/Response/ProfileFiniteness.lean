/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowSkewConclusion
import HCPoly.Provider.Response.ProfileWeakCarriers
import HCPoly.Provider.Bridge.LinearDrift

/-!
# Finiteness bridges for terminal response profiles

Fail-closed extended nonnegative profile quantities are converted to real
estimates only after an explicit finite upper bound has been established.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The response-row coefficient is nonnegative on a finite stationary
adapted-mean interval. -/
theorem profileRowGamma_nonneg [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {rhoDr : ℝ} {q : Mat d} {jStar s : ℤ}
    (hgrid : IsRoundedGrid jStar q) (hjs : jStar ≤ s)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ s → HasFiniteAdaptedMean P q k)
    {g Cd : ℝ} (hg : g < 1) (E : BlockMat d) (m0 : Mat d) :
    0 ≤ profileRowGamma P rhoDr q Cd g E jStar m0 s := by
  have hdrift : 0 ≤ linearDrift P rhoDr q jStar s :=
    Bridge.linearDrift_nonneg hstat hgrid le_rfl hjs hfin rhoDr
  have hdenOld : 0 < 1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hpow : (3 : ℝ) ^ (-(3 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith only [hpow]
  have hdenSource : 0 < (3 : ℝ) ^ (3 / 2 - g) - 1 := by
    have hpow : (1 : ℝ) < (3 : ℝ) ^ (3 / 2 - g) :=
      (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr
        (Or.inl ⟨by norm_num, by linarith only [hg]⟩)
    linarith only [hpow]
  have hold : 0 ≤ (1 + linearDrift P rhoDr q jStar s) /
      (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) :=
    div_nonneg (by linarith only [hdrift]) hdenOld.le
  have hsource : 0 ≤
      kappaRef E * boundaryConst Cd g m0 ^ 2 * 2 ^ 2 /
          ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) := by
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (Transport.zero_le_kappaRef E)
            (sq_nonneg (boundaryConst Cd g m0)))
          (sq_nonneg (2 : ℝ)))
        hdenSource.le)
      (Real.rpow_nonneg (by norm_num) _)
  rw [profileRowGamma]
  exact add_nonneg hold hsource

/-- An extended nonnegative quantity below `ofReal C` has the exact real
upper bound when `C` is nonnegative. -/
theorem toReal_le_of_le_ofReal {x : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (h : x ≤ ENNReal.ofReal C) : x.toReal ≤ C := by
  have htop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hC] at hreal

end

end Homogenization.HighContrast.Response
