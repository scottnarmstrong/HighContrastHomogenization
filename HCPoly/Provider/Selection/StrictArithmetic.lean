/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.StrictPrefix

/-!
# Arithmetic inputs for strict selector termination

The aspect-ratio entry term is absorbed by the logarithmic scale parameter,
and every geometrically valid selector state has nonnegative potential.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The identity-grid determinant entry is absorbed by `log 72` times the
base-three aspect-ratio scale. -/
theorem log_twentyFour_mul_le_log_seventyTwo_mul_logb
    {E : BlockMat d} {Lam : ℝ} (hPi : 1 ≤ aspectRatio E)
    (hLam : Lam = Real.logb 3 (2 + aspectRatio E)) :
    Real.log (24 * aspectRatio E) ≤ Real.log 72 * Lam := by
  have hPiPos : 0 < aspectRatio E := lt_of_lt_of_le zero_lt_one hPi
  have hlogThreePos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogTwentyFourPos : 0 < Real.log 24 := Real.log_pos (by norm_num)
  have hLamOne : 1 ≤ Lam := by
    rw [hLam]
    exact ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hlogScale : Real.log (2 + aspectRatio E) = Lam * Real.log 3 := by
    rw [hLam, Real.logb]
    field_simp [ne_of_gt hlogThreePos]
  have hlogSeventyTwo : Real.log 72 = Real.log 24 + Real.log 3 := by
    rw [show (72 : ℝ) = 24 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  calc
    Real.log (24 * aspectRatio E) = Real.log 24 + Real.log (aspectRatio E) :=
      Real.log_mul (by norm_num) (ne_of_gt hPiPos)
    _ ≤ Real.log 24 + Real.log (2 + aspectRatio E) := by
      have hPiAdd : aspectRatio E ≤ 2 + aspectRatio E := by
        linarith only
      have hlogPi : Real.log (aspectRatio E) ≤
          Real.log (2 + aspectRatio E) := Real.log_le_log hPiPos hPiAdd
      linarith only [hlogPi]
    _ = Real.log 24 + Lam * Real.log 3 := by rw [hlogScale]
    _ ≤ Lam * Real.log 24 + Lam * Real.log 3 := by
      have hscale := mul_le_mul_of_nonneg_right hLamOne hlogTwentyFourPos.le
      linarith only [hscale]
    _ = Real.log 72 * Lam := by rw [hlogSeventyTwo]; ring

/-- Positive witness and base metrics make the selector potential
nonnegative. -/
theorem statePotential_nonneg_of_posDef
    [Nonempty (Fin d)] {P : Measure (CoeffSpace d)} {jStar : ℤ}
    {S : State d}
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g))
    (hmu : S.mu.PosDef) (hbase : (toFullBlockMat S.baseMean).PosDef) :
    0 ≤ statePotential P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      w.alphaW w.alphaX w.alphaFresh w.alphaSearch S := by
  have hwork : 0 ≤ stateWork P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) c.etaReady jStar S := by
    rw [stateWork_eq]
    apply Real.log_nonneg
    have hterm : 0 ≤ c.etaReady⁻¹ *
        (portableProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) S.q jStar S.checkpoint S.cursor).toReal :=
      mul_nonneg (inv_nonneg.mpr c.etaReady_pos.le) ENNReal.toReal_nonneg
    linarith only [hterm]
  have hproj : 0 ≤ stateProjectiveDistance S := by
    rw [stateProjectiveDistance_eq]
    exact projDist_nonneg hmu (posDef_canonMetric hbase)
  rw [statePotential_eq]
  have hfresh : 0 ≤ if S.phase = Phase.fresh then w.alphaFresh else 0 := by
    split
    · exact w.alphaFresh_pos.le
    · exact le_rfl
  have hsearch : 0 ≤ if S.phase = Phase.search then w.alphaSearch else 0 := by
    split
    · exact w.alphaSearch_pos.le
    · exact le_rfl
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg (mul_nonneg w.alphaW_pos.le hwork) (Nat.cast_nonneg _))
          (mul_nonneg w.alphaX_nonneg hproj)) hfresh) hsearch

end

end Homogenization.HighContrast.Selection
