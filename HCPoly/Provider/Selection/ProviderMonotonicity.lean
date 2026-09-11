/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.ProviderData
import HCPoly.Provider.Transport.TransportCoefficients

/-!
# Upward closure of selector provider constants

The transport proposition supplies an upward-closed constant.  This adapter
records that closure at the bundled conclusion used by the selector, allowing
independently chosen bridge and transport constants to be replaced by a common
maximum.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- Enlarging the transport coefficient preserves its complete analytic
conclusion. -/
theorem TransportProviderData.enlargeConstant {d Q Ltr : ℕ}
    {g rhoMax a Khop Ctr Ctr' : ℝ}
    (raw : TransportProviderData d g Q rhoMax a Khop Ctr Ltr)
    (hCtr : Ctr ≤ Ctr') :
    TransportProviderData d g Q rhoMax a Khop Ctr' Ltr := by
  refine ⟨raw.one_le_Ltr, raw.Ctr_pos.trans_le hCtr, ?_⟩
  intro l0 hl0 Cd hCd P E Ψ K S hprob hstat hunit hdag jStar M hwin Y hY
    mu mu' hmu hmu' hratio rchk u hjchk hchku hcont
  obtain ⟨hdefined, hmean, hconclusion⟩ := raw.law l0 hl0 Cd hCd P E Ψ K S
    hprob hstat hunit hdag jStar M hwin Y hY mu mu' hmu hmu' hratio rchk u
    hjchk hchku hcont
  refine ⟨hdefined, hmean, ?_⟩
  intro etaX hetaX hetaXquarter hlo hhi
  obtain ⟨hhistory, hgramLo, hgramHi, hgramLo', hgramHi', hdetLo, hdetHi⟩ :=
    hconclusion etaX hetaX hetaXquarter hlo hhi
  have hbuf2 : 0 ≤ (3 : ℝ) ^ (2 * a * (l0 : ℝ)) := by positivity
  have hbuf1 : 0 ≤ (3 : ℝ) ^ (a * (l0 : ℝ)) := by positivity
  have hD : 1 ≤ transportSrcCoeff Cd g E jStar mu mu' :=
    Transport.one_le_transportSrcCoeff (zero_le_one.trans hCd) hdag.g_mem.2 E jStar mu mu'
  have hrem : 0 ≤ transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
      (u + (l0 : ℤ)) := by
    rw [transportSrcRemainder]
    exact mul_nonneg
      (add_nonneg (zero_le_one.trans hD)
        (Real.rpow_nonneg (zero_le_one.trans hD) (Q : ℝ)))
      (Real.rpow_nonneg (by norm_num) _)
  have hcoef2 : Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ)) ≤
      Ctr' * (3 : ℝ) ^ (2 * a * (l0 : ℝ)) :=
    mul_le_mul_of_nonneg_right hCtr hbuf2
  have hcoefX : Ctr * etaX ≤ Ctr' * etaX :=
    mul_le_mul_of_nonneg_right hCtr hetaX
  have hcoefR : Ctr * (3 : ℝ) ^ (a * (l0 : ℝ)) *
      transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
        (u + (l0 : ℤ)) ≤
      Ctr' * (3 : ℝ) ^ (a * (l0 : ℝ)) *
        transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
          (u + (l0 : ℤ)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCtr hbuf1) hrem
  have hhistory' := hhistory.trans <| add_le_add
    (add_le_add
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef2) le_rfl)
      (ENNReal.ofReal_le_ofReal hcoefX))
    (ENNReal.ofReal_le_ofReal hcoefR)
  exact ⟨hhistory', hgramLo, hgramHi, hgramLo', hgramHi', hdetLo, hdetHi⟩

end

end Homogenization.HighContrast.Selection
