/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ScaleFacts
import HCPoly.Provider.PortableHistory.Geometric

/-!
# Structural constant for the two-grid bridge

The comparison and shifted-drift estimates use one constant depending only on
the dimension and the growth exponent.  This file chooses it after collecting
the eight deterministic coefficients that occur in those estimates.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

noncomputable section

/-- There is one positive structural constant dominating every coefficient in
the upper comparison, lower comparison, and shifted drift. -/
theorem exists_bridge_constant (d : ℕ) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ 1 ≤ C ∧
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
          (6 * (d : ℝ) * Real.sqrt d) ≤ C ∧
      18 * (d : ℝ) * Real.sqrt d ≤ C ∧
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
          (3 * (2 * (d : ℝ) * Real.sqrt d +
              (2 * (d : ℝ) * Real.sqrt d) *
                (2 * (d : ℝ) * Real.sqrt d) * 2 *
                  (1 + 6 * Real.sqrt d) ^ (d - 1)) +
            2 * (d : ℝ) * Real.sqrt d) ≤ C ∧
      18 * (d : ℝ) * Real.sqrt d *
          (2 * (d : ℝ) * Real.sqrt d +
            (2 * (d : ℝ) * Real.sqrt d) *
              (2 * (d : ℝ) * Real.sqrt d) * 2 *
                (1 + 6 * Real.sqrt d) ^ (d - 1)) ≤ C ∧
      4 * (d : ℝ) *
          (1 / (1 - (3 : ℝ) ^ (-initExpRhoDr g))) ≤ C ∧
      2 * ((6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
          (1 / (1 - (3 : ℝ) ^ (-initExpRhoDr g))) *
          (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))) ≤ C ∧
      2 * ((1 / (1 - (3 : ℝ) ^ (-initExpRhoDr g))) +
          (6 * (d : ℝ) * Real.sqrt d) *
            (1 / (1 - (3 : ℝ) ^ (-initExpRhoDr g))) *
            (1 / (1 - (3 : ℝ) ^ (-(1 - initExpRhoDr g))))) ≤ C ∧
      2 * (2 * (d : ℝ) +
          (18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ))) ≤ C := by
  let rho : ℝ := initExpRhoDr g
  let Cg : ℝ := 2 * (d : ℝ) * Real.sqrt d +
    (2 * (d : ℝ) * Real.sqrt d) *
      (2 * (d : ℝ) * Real.sqrt d) * 2 *
        (1 + 6 * Real.sqrt d) ^ (d - 1)
  let D0 : ℝ := 2 * (d : ℝ) * Real.sqrt d
  let Urow : ℝ := (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
    (6 * (d : ℝ) * Real.sqrt d)
  let Usrc : ℝ := 18 * (d : ℝ) * Real.sqrt d
  let Lrow : ℝ := (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * (3 * Cg + D0)
  let Lsrc : ℝ := 18 * (d : ℝ) * Real.sqrt d * Cg
  let Seta : ℝ := 4 * (d : ℝ) * (1 / (1 - (3 : ℝ) ^ (-rho)))
  let Smass : ℝ := 2 * ((6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
    (1 / (1 - (3 : ℝ) ^ (-rho))) *
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))))
  let Sdrift : ℝ := 2 * ((1 / (1 - (3 : ℝ) ^ (-rho))) +
    (6 * (d : ℝ) * Real.sqrt d) *
      (1 / (1 - (3 : ℝ) ^ (-rho))) *
      (1 / (1 - (3 : ℝ) ^ (-(1 - rho)))))
  let Ssrc : ℝ := 2 * (2 * (d : ℝ) +
    (18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)))
  let C : ℝ := 1 + Urow + Usrc + Lrow + Lsrc + Seta + Smass + Sdrift + Ssrc
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact initExpRhoDr_pos hg
  have hrho1 : rho < 1 := by
    have h := initExpRhoDr_lt_one_sub hg
    dsimp only [rho]
    linarith only [h, hg.1]
  have hG : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-rho)) :=
    div_nonneg zero_le_one (sub_nonneg.mpr (PortableHistory.geom_ratio_lt_one hrho).le)
  have hGcomp : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 - rho))) :=
    div_nonneg zero_le_one (sub_nonneg.mpr
      (PortableHistory.geom_ratio_lt_one (by linarith only [hrho1])).le)
  have hGone : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))) := by norm_num
  have hCg : 0 ≤ Cg := by dsimp only [Cg]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hUrow : 0 ≤ Urow := by dsimp only [Urow]; positivity
  have hUsrc : 0 ≤ Usrc := by dsimp only [Usrc]; positivity
  have hLrow : 0 ≤ Lrow := by dsimp only [Lrow]; positivity
  have hLsrc : 0 ≤ Lsrc := by dsimp only [Lsrc]; positivity
  have hSeta : 0 ≤ Seta := by dsimp only [Seta]; positivity
  have hSmass : 0 ≤ Smass := by dsimp only [Smass]; positivity
  have hSdrift : 0 ≤ Sdrift := by dsimp only [Sdrift]; positivity
  have hSsrc : 0 ≤ Ssrc := by dsimp only [Ssrc]; positivity
  have hC : 0 < C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLrow, hLsrc, hSeta, hSmass, hSdrift, hSsrc]
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLrow, hLsrc, hSeta, hSmass, hSdrift, hSsrc]
  have hUrowC : Urow ≤ C := by
    dsimp only [C]
    linarith only [hUsrc, hLrow, hLsrc, hSeta, hSmass, hSdrift, hSsrc]
  have hUsrcC : Usrc ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hLrow, hLsrc, hSeta, hSmass, hSdrift, hSsrc]
  have hLrowC : Lrow ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLsrc, hSeta, hSmass, hSdrift, hSsrc]
  have hLsrcC : Lsrc ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLrow, hSeta, hSmass, hSdrift, hSsrc]
  have hSetaC : Seta ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLrow, hLsrc, hSmass, hSdrift, hSsrc]
  have hSmassC : Smass ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLrow, hLsrc, hSeta, hSdrift, hSsrc]
  have hSdriftC : Sdrift ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLrow, hLsrc, hSeta, hSmass, hSsrc]
  have hSsrcC : Ssrc ≤ C := by
    dsimp only [C]
    linarith only [hUrow, hUsrc, hLrow, hLsrc, hSeta, hSmass, hSdrift]
  refine ⟨C, hC, hC1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Urow] using hUrowC
  · simpa only [Usrc] using hUsrcC
  · simpa only [Lrow, Cg, D0] using hLrowC
  · simpa only [Lsrc, Cg] using hLsrcC
  · simpa only [Seta, rho] using hSetaC
  · simpa only [Smass, rho] using hSmassC
  · simpa only [Sdrift, rho] using hSdriftC
  · simpa only [Ssrc] using hSsrcC

end

end Bridge
end HighContrast
end Homogenization
