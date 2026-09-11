/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileMaximumLp
import HCPoly.Provider.Response.ConstantSkewProfiles

/-!
# Complete maximum bounds after skew recentering

Simultaneous shear congruence of the samplewise blocks and terminal reference
preserves the all-scale maximum.  Its pointwise and `L^Q` estimates can thus be
read directly from the portable, unhatted terminal histories.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The recentered complete maximum is bounded pointwise by the total maximum
and terminal drift. -/
theorem diagonalWeakMaximum_subSkew_le_profileTotalMaximum_add_drift
    [NeZero d]
    {P : Measure (CoeffSpace d)} {rhoMax rhoDr rhoWn : ℝ}
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn) {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ}
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)))
    (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d) :
    diagonalWeakMaximum rhoWn q t
        (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg) ≤
      profileTotalMaximum P rhoMax q jStar t (adaptedMean P q t) a +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) := by
  rw [diagonalWeakMaximum_subSkew hq]
  exact diagonalWeakMaximum_le_profileTotalMaximum_add_drift
    hrhoMax hrhoDr hrhoDrWn hq hEt hmono a

/-- The recentered complete maximum has the total-history `L^Q` bound. -/
theorem eLpNorm_diagonalWeakMaximum_subSkew_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q rhoMax rhoDr rhoWn : ℝ} (hQ : 1 ≤ Q)
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn) {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (hjt : jStar ≤ t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)))
    (g : Mat d) (hg : IsSkewMat g) :
    eLpNorm
        (fun a ↦ diagonalWeakMaximum rhoWn q t
          (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg))
        (ENNReal.ofReal Q) P ≤
      profileTotalHistory P Q rhoMax q jStar t (adaptedMean P q t) ^ Q⁻¹ +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) := by
  have hfun :
      (fun a ↦ diagonalWeakMaximum rhoWn q t
        (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg)) =
        diagonalWeakMaximum rhoWn q t (adaptedMean P q t) := by
    funext a
    exact diagonalWeakMaximum_subSkew hq rhoWn t (adaptedMean P q t) a g hg
  rw [hfun]
  exact eLpNorm_diagonalWeakMaximum_le_profile hQ hrhoMax hrhoDr
    hrhoDrWn hq hjt hEt hmono

/-- The recentered complete maximum has the centered/source/drift `L^Q`
bound. -/
theorem eLpNorm_diagonalWeakMaximum_subSkew_le_centered_source_drift
    [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q rhoMax rhoDr rhoWn : ℝ} (hQ : 1 ≤ Q)
    (hrhoMax : rhoMax ≤ rhoWn) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrWn : rhoDr ≤ rhoWn) {q : Mat d} (hq : q.PosDef)
    {jStar t : ℤ} (hjt : jStar ≤ t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)))
    (g : Mat d) (hg : IsSkewMat g) :
    eLpNorm
        (fun a ↦ diagonalWeakMaximum rhoWn q t
          (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg))
        (ENNReal.ofReal Q) P ≤
      centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ +
        profileSourceMoment P Q rhoMax q jStar t (adaptedMean P q t) +
        ENNReal.ofReal (linearDrift P rhoDr q jStar t) := by
  have hfun :
      (fun a ↦ diagonalWeakMaximum rhoWn q t
        (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg)) =
        diagonalWeakMaximum rhoWn q t (adaptedMean P q t) := by
    funext a
    exact diagonalWeakMaximum_subSkew hq rhoWn t (adaptedMean P q t) a g hg
  rw [hfun]
  exact eLpNorm_diagonalWeakMaximum_le_centered_source_drift hQ hrhoMax
    hrhoDr hrhoDrWn hq hjt hEt hmono

end

end Homogenization.HighContrast.Response
