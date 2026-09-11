/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.FixedGridWindowAccount
import HCPoly.Provider.Quenched.SmallContrastAbsorptionChoice
import HCPoly.Provider.Quenched.SmallContrastAdjointMirrors
import HCPoly.Provider.Quenched.SmallContrastAlignedGeometry
import HCPoly.Provider.Quenched.SmallContrastAnnealedEnvelope
import HCPoly.Provider.Quenched.SmallContrastAverageDrops
import HCPoly.Provider.Quenched.SmallContrastCenteringCap
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope
import HCPoly.Provider.Quenched.SmallContrastEntrySupply
import HCPoly.Provider.Quenched.SmallContrastFusionStep
import HCPoly.Provider.Quenched.SmallContrastMeanDropCarrier
import HCPoly.Provider.Quenched.SmallContrastOneStepHub
import HCPoly.Provider.Quenched.SmallContrastRowAtCenters
import HCPoly.Provider.Quenched.SmallContrastSingleCellVariance
import HCPoly.Provider.Quenched.SmallContrastTerminalComparability
import HCPoly.Provider.Quenched.SmallContrastWeakCap
import HCPoly.Provider.Quenched.SmallContrastWeakValue
import HCPoly.Provider.Response.DiagonalWeakNormAdjointAlgebra
import HCPoly.Provider.Response.PreYoungFixedGridCells
import HCPoly.Provider.Response.ProfileRowOscillationSum
import HCPoly.Provider.Response.ProfileRowSchur
import HCPoly.Provider.Response.ProfileRowSkewCarriers

/-!
# The two adapters of the closing pass records exactly one shape mismatch in the fusion's argument table, and
one identification that is definitional.  Both are here.

* **The rate adapter.**  `weakValueSharpMajorant_le_three_group_summed_at_level`
  produces its drop bound at the rooted-drop rate `contrastAlpha g`, while
  `hrec_line_of_one_step_isotropy_sharp_at_jb_src` consumes it at the recursion rate
  `recursionAlpha g ≤ contrastAlpha g`.  Since `iterationDropSum` is increasing
  in its ratio, the move is `iterationDropSum_mono_r` — two lines, and neither
  side of the interface changes.

* **The base identification.**  `weakValueSharpMajorant_le_three_group_summed_at_level` *is* the square of its
  base, so the `hmaj` position of `hrec_line_of_one_step_isotropy_sharp_at_jb_src` is stage 4's
  conclusion read through `rfl` at `W := weakValueBase …`.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The rate adapter.**  A drop bound at the rooted-drop rate is a drop bound
at the recursion rate. -/
theorem iterationDropSum_alpha_adapter {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) {g : ℝ} (hg1 : g ≤ 1) (n : ℕ) :
    iterationDropSum ((3 : ℝ) ^ (-contrastAlpha g)) F n ≤
      iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g)) F n := by
  refine iterationDropSum_mono_r hFmono
    (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_ n
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h := recursionAlpha_le_contrastAlpha g hg1
  linarith only [h]

/-- The drop constant of the summed split is nonnegative. -/
theorem weakDropConstant_nonneg (d : ℕ) {M L alpha cD delta : ℝ}
    (halpha0 : 0 < alpha) (hcD : 0 ≤ cD) (hdelta : 0 ≤ delta) :
    0 ≤ weakDropConstant (d := d) M L alpha cD delta := by
  have hlt : (3 : ℝ) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [halpha0])
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-alpha) := by linarith only [hlt]
  have hinv : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-alpha))⁻¹ :=
    le_of_lt (inv_pos.mpr hden)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [weakDropConstant]
  have h1 : (0 : ℝ) ≤ delta * halfGeom * (cD * halfGeom) :=
    mul_nonneg (mul_nonneg hdelta halfGeom_pos.le)
      (mul_nonneg hcD halfGeom_pos.le)
  have h2 : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-alpha))⁻¹ *
      (2 * (d : ℝ) * (cD * (1 - (3 : ℝ) ^ (-alpha))⁻¹)) := by
    refine mul_nonneg hinv ?_
    exact mul_nonneg (by linarith only [hd0]) (mul_nonneg hcD hinv)
  have h3 : (0 : ℝ) ≤ 2 * (16 * M * Real.sqrt L) ^ 2 := by positivity
  exact mul_nonneg h3 (by linarith only [h1, h2])

/-- **The drop bound at the recursion rate.**  This is the `hwsq` position of
`hrec_line_of_one_step_isotropy_sharp_at_jb_src`, from the summed split's output. -/
theorem hwsq_at_recursionAlpha {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) {g : ℝ} (hg1 : g ≤ 1)
    {M L cD delta w : ℝ} {n : ℕ}
    (halpha0 : 0 < contrastAlpha g) (hcD : 0 ≤ cD) (hdelta : 0 ≤ delta)
    (hw : w ^ 2 ≤ weakDropConstant (d := d) M L (contrastAlpha g) cD delta *
      iterationDropSum ((3 : ℝ) ^ (-contrastAlpha g)) F n) :
    w ^ 2 ≤ weakDropConstant (d := d) M L (contrastAlpha g) cD delta *
      iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g)) F n := by
  refine le_trans hw ?_
  exact mul_le_mul_of_nonneg_left (iterationDropSum_alpha_adapter hFmono hg1 n)
    (weakDropConstant_nonneg d halpha0 hcD hdelta)

end

end Homogenization.HighContrast.Quenched
