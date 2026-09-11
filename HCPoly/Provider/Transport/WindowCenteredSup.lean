/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowCenteredCells
import HCPoly.Provider.Transport.WindowMomentBound

/-!
# The centered displays of the whole-cell regime

The pathwise bound of the retained family is a multiple of `Y_P + \E[Y_P]`, and
the centered bound for the early target cells and its source-tail form are what
that becomes under the `L^Q` norm and under the mixed source-tail relation.

For the `L^Q` display the mean is a constant, whose `L^Q` norm on a probability
space is itself, and the mean of a nonnegative variable is below its `L^Q` norm;
so the sum costs a factor two and the display holds with
`C_{d,Q} = 2(2d)^{1/Q}`.

For the tail display the decomposition is `Y_P = 1 + (Y_P - 1)`.  The
deterministic part is `1 + \E[Y_P]`, which the first-moment display bounds by
`2 + a_{j_*}^{\mathcal S}\mathfrak M_1(\overline K_{\mathcal S})` — exactly the
shift the printed clause writes — and the random part is a multiple of the
multiplier's excess, which carries the source gauge's tail at the remainder
scale.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-! ## From a pathwise bound by a multiple of `Y_P + \E[Y_P]` -/

/-- **The `L^Q` norm of a quantity dominated by `c(Y_P+\E[Y_P])`.**  The constant
part is its own `L^Q` norm on a probability space, and the mean is below the
`L^Q` norm, so the sum costs a factor two. -/
theorem eLpNorm_le_of_ae_le_mul_add [IsProbabilityMeasure P] {X : CoeffSpace d → ℝ≥0∞}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {c : ℝ} (hc : 0 ≤ c) {Q : ℝ}
    (hQ : 1 ≤ Q) (hle : ∀ᵐ a ∂P, X a ≤ ENNReal.ofReal (c * (Y a + ∫ b, Y b ∂P))) :
    eLpNorm X (ENNReal.ofReal Q) P ≤ ENNReal.ofReal (2 * c) * lqNorm P Q Y := by
  have hint := integrable_of_isWindowMultiplier hY
  have hmean : (0 : ℝ) ≤ ∫ b, Y b ∂P :=
    le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le one_pos hQ
  have hmono : eLpNorm X (ENNReal.ofReal Q) P ≤
      eLpNorm ((fun a => c * Y a) + fun _ => c * ∫ b, Y b ∂P) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_enorm_ae ?_
    filter_upwards [hle] with a ha
    have hnn : (0 : ℝ) ≤ c * Y a + c * ∫ b, Y b ∂P :=
      add_nonneg (mul_nonneg hc (le_trans zero_le_one (hY.one_le a)))
        (mul_nonneg hc hmean)
    show X a ≤ ‖c * Y a + c * ∫ b, Y b ∂P‖ₑ
    rw [Real.enorm_eq_ofReal hnn]
    exact ha.trans (le_of_eq (congrArg ENNReal.ofReal (by ring)))
  refine hmono.trans ?_
  have hadd := eLpNorm_add_le (μ := P) (p := ENNReal.ofReal Q)
    (hint.const_mul c).aestronglyMeasurable
    (aestronglyMeasurable_const (b := c * ∫ b, Y b ∂P)) (ENNReal.one_le_ofReal.mpr hQ)
  refine hadd.trans ?_
  have h1 : eLpNorm (fun a => c * Y a) (ENNReal.ofReal Q) P =
      ENNReal.ofReal c * lqNorm P Q Y := by
    rw [show (fun a => c * Y a) = c • Y from rfl, eLpNorm_const_smul,
      Real.enorm_eq_ofReal hc]
    rfl
  have h2 : eLpNorm (fun _ : CoeffSpace d => c * ∫ b, Y b ∂P) (ENNReal.ofReal Q) P =
      ENNReal.ofReal c * ENNReal.ofReal (∫ b, Y b ∂P) := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hQ0).ne' (IsProbabilityMeasure.ne_zero P),
      measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_eq_ofReal (mul_nonneg hc hmean), ENNReal.ofReal_mul hc]
  rw [h1, h2, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc ENNReal.ofReal c * lqNorm P Q Y +
        ENNReal.ofReal c * ENNReal.ofReal (∫ b, Y b ∂P)
      ≤ ENNReal.ofReal c * lqNorm P Q Y + ENNReal.ofReal c * lqNorm P Q Y := by
        gcongr
        exact ofReal_integral_le_lqNorm hY hQ
    _ = ENNReal.ofReal 2 * ENNReal.ofReal c * lqNorm P Q Y := by
        rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
        ring

/-- **The mixed source tail of a quantity dominated by `c(Y_P+\E[Y_P])`.**  The
deterministic part `c(1+\E[Y_P])` is below the printed shift by the first-moment
display, and the random part is a multiple of the multiplier's excess. -/
theorem isShiftedBigOWithTop_of_ae_le_mul_add [IsProbabilityMeasure P]
    {X : CoeffSpace d → ℝ≥0∞}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ᵐ a ∂P, X a ≤ ENNReal.ofReal (c * (Y a + ∫ b, Y b ∂P))) :
    IsShiftedBigOWithTop P Ψ X
      (2 * c *
        (2 + sourceRemainderScale d jStar K * momentMultiplier 1 (growthBar K)))
      (2 * c * sourceRemainderScale d jStar K) := by
  have haS : (0 : ℝ) < sourceRemainderScale d jStar K :=
    zero_lt_sourceRemainderScale d jStar K
  have hMo : (0 : ℝ) < momentMultiplier 1 (growthBar K) :=
    zero_lt_momentMultiplier (K := K) one_pos
  have hprod : (0 : ℝ) ≤
      sourceRemainderScale d jStar K * momentMultiplier 1 (growthBar K) :=
    (mul_pos haS hMo).le
  have hmeanle := integral_le_one_add_momentMultiplier hY
  refine ⟨fun a => c * (Y a - 1),
    fun a => mul_nonneg hc (by linarith only [hY.one_le a]), ?_, ?_⟩
  · filter_upwards [hle] with a ha
    refine ha.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA : 1 + (∫ b, Y b ∂P) ≤
        2 + sourceRemainderScale d jStar K * momentMultiplier 1 (growthBar K) := by
      linarith only [hmeanle]
    have hB := mul_le_mul_of_nonneg_left hA hc
    have hC : (0 : ℝ) ≤ c *
        (2 + sourceRemainderScale d jStar K * momentMultiplier 1 (growthBar K)) :=
      mul_nonneg hc (by linarith only [hprod])
    linarith only [hB, hC]
  · exact (hY.orlicz.const_mul hc).mono_scale
      (by linarith only [mul_nonneg hc haS.le])

/-! ## The four centered displays -/

section Family

variable (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
  (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
  (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {F : BlockMat d}
  (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {Q : ℝ} (hQ : 1 ≤ Q)
  {j : ℤ} (hj : jStar ≤ j) {W : Set (Set (Vec d))}
  (hWmem : ∀ V ∈ W, ∃ y : Vec d, V = adaptedCellTranslate (roundedGrid jStar nu) j y)
  (hWcont : ∀ V ∈ W, V ⊆ centeredCube d M)

include hCd hg hE hY hnu hq hF hFpd hQ hj hWmem hWcont in
/-- **The centered `L^Q` display of the whole-cell regime**, the centered bound
for the early target cells, with the constant `2(2d)^{1/Q}`. -/
theorem eLpNorm_cellFamilyCenteredSup_le [IsProbabilityMeasure P] :
    eLpNorm (cellFamilyCenteredSup P Q W F) (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F) *
        lqNorm P Q Y := by
  have hc : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (zero_le_boundaryConst hCd hg nu)) (PortableHistory.blockSize_nonneg hE hF hFpd)
  have hpath := ae_cellFamilyCenteredSup_le hCd hg hE hY hnu hq hF hFpd
    (lt_of_lt_of_le one_pos hQ) hj hWmem hWcont
  have h := eLpNorm_le_of_ae_le_mul_add (X := cellFamilyCenteredSup P Q W F) hY hc hQ
    (by filter_upwards [hpath] with a ha
        exact ha.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  rwa [show 2 * ((2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F) =
    2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F from by ring] at h

include hCd hg hE hY hnu hq hF hFpd hQ hj hWmem hWcont in
/-- **The adjoint centered `L^Q` display of the whole-cell regime.** -/
theorem eLpNorm_cellFamilyCenteredSupAdjoint_le [IsProbabilityMeasure P] :
    eLpNorm (cellFamilyCenteredSupAdjoint P Q W (blockReflect F)) (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F) *
        lqNorm P Q Y := by
  have hc : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (zero_le_boundaryConst hCd hg nu)) (PortableHistory.blockSize_nonneg hE hF hFpd)
  have hpath := ae_cellFamilyCenteredSupAdjoint_le hCd hg hE hY hnu hq hF hFpd
    (lt_of_lt_of_le one_pos hQ) hj hWmem hWcont
  have h := eLpNorm_le_of_ae_le_mul_add
    (X := cellFamilyCenteredSupAdjoint P Q W (blockReflect F)) hY hc hQ
    (by filter_upwards [hpath] with a ha
        exact ha.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  rwa [show 2 * ((2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F) =
    2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F from by ring] at h

include hCd hg hE hY hnu hq hF hFpd hQ hj hWmem hWcont in
/-- **The centered mixed source tail of the whole-cell regime**, the source-tail
form of the early-cell bound. -/
theorem isShiftedBigOWithTop_cellFamilyCenteredSup [IsProbabilityMeasure P] :
    IsShiftedBigOWithTop P Ψ (cellFamilyCenteredSup P Q W F)
      (2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F *
        (2 + sourceRemainderScale d jStar K * momentMultiplier 1 (growthBar K)))
      (2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F *
        sourceRemainderScale d jStar K) := by
  have hc : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (zero_le_boundaryConst hCd hg nu)) (PortableHistory.blockSize_nonneg hE hF hFpd)
  have hpath := ae_cellFamilyCenteredSup_le hCd hg hE hY hnu hq hF hFpd
    (lt_of_lt_of_le one_pos hQ) hj hWmem hWcont
  have h := isShiftedBigOWithTop_of_ae_le_mul_add
    (X := cellFamilyCenteredSup P Q W F) hY hc
    (by filter_upwards [hpath] with a ha
        exact ha.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  rwa [show 2 * ((2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F) =
    2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F from by ring] at h

include hCd hg hE hY hnu hq hF hFpd hQ hj hWmem hWcont in
/-- **The adjoint centered mixed source tail of the whole-cell regime.** -/
theorem isShiftedBigOWithTop_cellFamilyCenteredSupAdjoint [IsProbabilityMeasure P] :
    IsShiftedBigOWithTop P Ψ (cellFamilyCenteredSupAdjoint P Q W (blockReflect F))
      (2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F *
        (2 + sourceRemainderScale d jStar K * momentMultiplier 1 (growthBar K)))
      (2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F *
        sourceRemainderScale d jStar K) := by
  have hc : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (zero_le_boundaryConst hCd hg nu)) (PortableHistory.blockSize_nonneg hE hF hFpd)
  have hpath := ae_cellFamilyCenteredSupAdjoint_le hCd hg hE hY hnu hq hF hFpd
    (lt_of_lt_of_le one_pos hQ) hj hWmem hWcont
  have h := isShiftedBigOWithTop_of_ae_le_mul_add
    (X := cellFamilyCenteredSupAdjoint P Q W (blockReflect F)) hY hc
    (by filter_upwards [hpath] with a ha
        exact ha.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  rwa [show 2 * ((2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F) =
    2 * (2 * d : ℝ) ^ Q⁻¹ * boundaryConst Cd g nu * blockSize E F from by ring] at h

end Family

end

end Transport
end HighContrast
end Homogenization
