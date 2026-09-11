/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.AffineWeakGradient
import HCPoly.Analytic.EllipsoidGeometry
import HCPoly.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
import HCPoly.Provider.Quenched.CoupledMixingScaleDecay
import HCPoly.Provider.Regularity.AffineGradientQuotientInverse
import HCPoly.Provider.Regularity.H1aOpenSubsetGradientRealization
import HCPoly.Provider.Regularity.LiouvilleCubeRestriction
import HCPoly.Provider.Regularity.RoundedAffineFields
import HCPoly.Provider.Regularity.RoundedCenteredCoeffFamily
import HCPoly.Provider.Regularity.RoundedEllipsoidTriadicGeometry
import HCPoly.Provider.Regularity.RoundedEllipsoidWeightedNormBridge
import HCPoly.Provider.Regularity.RoundedFiniteEnergyENNRealBridge
import HCPoly.Provider.Regularity.RoundedPhysicalDirichletAffineResponse
import HCPoly.Provider.Regularity.RoundedWeakSolutionPullback
import HCPoly.Provider.Selection.EnclosureGeometry
import Homogenization.Probability.LocalEllipticitySlices

/-!
# Comparing the printed-order and root response scales

The printed-order recurrence and the root certificate differ only in their
dimension-and-order response constants.  The deterministic factor below
absorbs that difference before the coefficient law, matrix, and sample are
chosen.
-/

namespace Homogenization
namespace HighContrast
namespace Root

open Set

noncomputable section

open Certificate

/-- The law-free multiplier comparing the printed-order response constant to
the base response constant at rate `kappa`. -/
noncomputable def printOrderToBaseResponseScaleFactor
    (d : ℕ) (g kappa : ℝ) : ℝ :=
  max 1
    ((printOrderRoundedResponseAffineConstant d g /
      Transport.roundedOuterResponseAffineConstant d) ^ kappa⁻¹)

theorem one_le_printOrderToBaseResponseScaleFactor
    (d : ℕ) (g kappa : ℝ) :
    1 ≤ printOrderToBaseResponseScaleFactor d g kappa :=
  le_max_left _ _

private theorem roundedAffineLossAmplitude_print_eq_ratio_mul_base
    (d : ℕ) (g overlinePi : ℝ) :
    roundedAffineLossAmplitude
        (printOrderRoundedResponseAffineConstant d g) overlinePi =
      (printOrderRoundedResponseAffineConstant d g /
          Transport.roundedOuterResponseAffineConstant d) *
        roundedAffineLossAmplitude
          (Transport.roundedOuterResponseAffineConstant d) overlinePi := by
  unfold roundedAffineLossAmplitude
  field_simp [Transport.roundedOuterResponseAffineConstant_pos d |>.ne']

/-- The printed-order affine multiplier is bounded by a law-free factor times
the base-response multiplier.  The matrix condition number cancels from the
comparison. -/
theorem roundedAffineMultiplier_printOrder_le_factor_mul_base
    (d : ℕ) {g kappa overlinePi : ℝ}
    (hg : g ∈ Ico (0 : ℝ) 1) :
    roundedAffineMultiplier
        (printOrderRoundedResponseAffineConstant d g) overlinePi kappa ≤
      printOrderToBaseResponseScaleFactor d g kappa *
        roundedAffineMultiplier
          (Transport.roundedOuterResponseAffineConstant d) overlinePi kappa := by
  have hratio : 0 ≤
      printOrderRoundedResponseAffineConstant d g /
        Transport.roundedOuterResponseAffineConstant d :=
    div_nonneg (printOrderRoundedResponseAffineConstant_pos d hg).le
      (Transport.roundedOuterResponseAffineConstant_pos d).le
  have hbaseAmplitude : 0 ≤ roundedAffineLossAmplitude
      (Transport.roundedOuterResponseAffineConstant d) overlinePi := by
    exact mul_nonneg (Transport.roundedOuterResponseAffineConstant_pos d).le
      (Real.sqrt_nonneg _)
  rw [roundedAffineMultiplier, roundedAffineMultiplier,
    roundedAffineLossAmplitude_print_eq_ratio_mul_base d g overlinePi,
    Real.mul_rpow hratio hbaseAmplitude]
  unfold printOrderToBaseResponseScaleFactor
  let u : ℝ :=
    (printOrderRoundedResponseAffineConstant d g /
      Transport.roundedOuterResponseAffineConstant d) ^ kappa⁻¹
  let v : ℝ :=
    roundedAffineLossAmplitude
      (Transport.roundedOuterResponseAffineConstant d) overlinePi ^ kappa⁻¹
  have hu : 0 ≤ u := by
    exact Real.rpow_nonneg hratio _
  have hv : 0 ≤ v := by
    exact Real.rpow_nonneg hbaseAmplitude _
  change max 1 (u * v) ≤ max 1 u * max 1 v
  apply max_le
  · calc
      1 = 1 * 1 := by ring
      _ ≤ max 1 u * max 1 v :=
        mul_le_mul (le_max_left _ _) (le_max_left _ _)
          (by norm_num) (zero_le_one.trans (le_max_left _ _))
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _)
      hv (hu.trans (le_max_right _ _))

/-- At every sample with a unit-lower-bounded source scale, the printed-order
common scale is at most a law-free multiple of the root common scale. -/
theorem printOrderCommonScale_le_factor_mul_baseCommonScale
    {d : ℕ} {g sourceAmplitude target kappa : ℝ}
    {abar : Mat d} {X : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (hg : g ∈ Ico (0 : ℝ) 1) (hkappa : 0 < kappa)
    (hX : 1 ≤ X a) :
    printOrderCommonQuantitativeAffineScale
        d g sourceAmplitude target kappa abar X a ≤
      printOrderToBaseResponseScaleFactor d g kappa *
        commonQuantitativeAffineScale sourceAmplitude target kappa
          (Transport.roundedOuterResponseAffineConstant d)
          (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
          kappa X a := by
  have htarget : 0 ≤ targetedQuantitativeEffectiveScale
      sourceAmplitude target kappa X a := by
    exact zero_le_one.trans (one_le_powerLossRandomScale
      (one_le_amplitudeReductionFactor sourceAmplitude target) hkappa hX)
  rw [printOrderCommonQuantitativeAffineScale,
    commonQuantitativeAffineScale, roundedAffineEffectiveScale]
  calc
    roundedAffineMultiplier
          (printOrderRoundedResponseAffineConstant d g)
          (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
          kappa *
        targetedQuantitativeEffectiveScale
          sourceAmplitude target kappa X a ≤
      (printOrderToBaseResponseScaleFactor d g kappa *
          roundedAffineMultiplier
            (Transport.roundedOuterResponseAffineConstant d)
            (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
            kappa) *
        targetedQuantitativeEffectiveScale
          sourceAmplitude target kappa X a :=
      mul_le_mul_of_nonneg_right
        (roundedAffineMultiplier_printOrder_le_factor_mul_base
          d hg) htarget
    _ = printOrderToBaseResponseScaleFactor d g kappa *
        (roundedAffineMultiplier
            (Transport.roundedOuterResponseAffineConstant d)
            (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
            kappa *
          targetedQuantitativeEffectiveScale
            sourceAmplitude target kappa X a) := by ring

/-- The recurrence-start scale of a terminal surface lies below a deterministic
multiple of the base-response scale exposed by the root. -/
theorem
    PrintOrderDecoupledFiniteTerminalSurface.printOrderScale_le_factor_mul_rootScale
    {d : ℕ} [NeZero d] {g c kappa Cid : ℝ}
    {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (surface : PrintOrderDecoupledFiniteTerminalSurface
      d g c kappa Cid abar a x)
    (hg : g ∈ Ico (0 : ℝ) 1) :
    printOrderCommonQuantitativeAffineScale d g surface.sourceAmplitude
        (correctorTargetAmplitude c kappa) kappa abar surface.X a ≤
      printOrderToBaseResponseScaleFactor d g kappa * x := by
  obtain ⟨_, _, _, _, _, hkappa, hX, _, _⟩ := surface.sourceCertificate
  calc
    printOrderCommonQuantitativeAffineScale d g surface.sourceAmplitude
          (correctorTargetAmplitude c kappa) kappa abar surface.X a ≤
        printOrderToBaseResponseScaleFactor d g kappa *
          commonQuantitativeAffineScale surface.sourceAmplitude
            (correctorTargetAmplitude c kappa) kappa
            (Transport.roundedOuterResponseAffineConstant d)
            (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
            kappa surface.X a :=
      printOrderCommonScale_le_factor_mul_baseCommonScale hg hkappa hX
    _ = printOrderToBaseResponseScaleFactor d g kappa * x :=
      congrArg (fun y : ℝ ↦
        printOrderToBaseResponseScaleFactor d g kappa * y)
        surface.rootScale_eq.symm

/-- The recurrence-start generation is at most the root-start generation plus
one deterministic delay.  In particular, the delay is independent of the
probability law, homogenized matrix, coefficient sample, and source scale. -/
theorem
    PrintOrderDecoupledFiniteTerminalSurface.printOrderStartIndex_le_rootStart_add_delay
    {d : ℕ} [NeZero d] {g c kappa Cid : ℝ}
    {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (surface : PrintOrderDecoupledFiniteTerminalSurface
      d g c kappa Cid abar a x)
    (hg : g ∈ Ico (0 : ℝ) 1) :
    Quenched.triadicCeilingIndex
        (printOrderCommonQuantitativeAffineScale d g surface.sourceAmplitude
          (correctorTargetAmplitude c kappa) kappa abar surface.X a) ≤
      Quenched.triadicCeilingIndex x +
        Quenched.triadicCeilingIndex
          (printOrderToBaseResponseScaleFactor d g kappa) := by
  obtain ⟨_, _, _, _, _, hkappa, hX, _, _⟩ := surface.sourceCertificate
  let xPrint : ℝ := printOrderCommonQuantitativeAffineScale d g
    surface.sourceAmplitude (correctorTargetAmplitude c kappa) kappa
    abar surface.X a
  let A : ℝ := printOrderToBaseResponseScaleFactor d g kappa
  have hxOne : 1 ≤ x := by
    calc
      1 ≤ commonQuantitativeAffineScale surface.sourceAmplitude
          (correctorTargetAmplitude c kappa) kappa
          (Transport.roundedOuterResponseAffineConstant d)
          (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
          kappa surface.X a :=
        one_le_commonQuantitativeAffineScale hkappa hX
      _ = x := surface.rootScale_eq.symm
  have hAOne : 1 ≤ A := by
    exact one_le_printOrderToBaseResponseScaleFactor d g kappa
  have hPrintOne : 1 ≤ xPrint := by
    exact one_le_commonQuantitativeAffineScale hkappa hX
  have hPrintLe : xPrint ≤ A * x := by
    exact
      Homogenization.HighContrast.Root.PrintOrderDecoupledFiniteTerminalSurface.printOrderScale_le_factor_mul_rootScale
        surface hg
  have hxCeil : x ≤ (3 : ℝ) ^ Quenched.triadicCeilingIndex x :=
    Quenched.le_pow_triadicCeilingIndex hxOne
  have hACeil : A ≤ (3 : ℝ) ^ Quenched.triadicCeilingIndex A :=
    Quenched.le_pow_triadicCeilingIndex hAOne
  apply Quenched.triadicCeilingIndex_le_of_le_pow hPrintOne
  calc
    xPrint ≤ A * x := hPrintLe
    _ ≤ (3 : ℝ) ^ Quenched.triadicCeilingIndex A *
        (3 : ℝ) ^ Quenched.triadicCeilingIndex x :=
      mul_le_mul hACeil hxCeil (zero_le_one.trans hxOne)
        (by positivity)
    _ = (3 : ℝ) ^
        (Quenched.triadicCeilingIndex x +
          Quenched.triadicCeilingIndex A) := by
      rw [pow_add, mul_comm]

end

end Root
end HighContrast
end Homogenization
