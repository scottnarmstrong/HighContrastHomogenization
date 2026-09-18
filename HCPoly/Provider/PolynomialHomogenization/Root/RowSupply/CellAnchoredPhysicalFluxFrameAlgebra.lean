/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Analytic.AffineH10
import HCPoly.Analytic.AffineNegSobolevNorm
import HCPoly.Analytic.H1a0ToH10
import HCPoly.Provider.Initialization.IdentityGrid
import HCPoly.Provider.PolynomialHomogenization.AffineCoeffFamily
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootCoefficient
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootEnclosure
import HCPoly.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
import HCPoly.Provider.PolynomialHomogenization.RuledLocalizationAssembly
import HCPoly.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.CenteredIndicatorExtensionBasic
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.EpsilonAffineDoubledResponseRealization
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.FixedParentObservationResponse
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.OuterC0MatrixScaleIdentity
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxRateAggregationReduction
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.PrintCellAnchoredObservationResponse
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.PrintDirectGradientResponsePrice
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.RealScaleTriadicBracket
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupplyAssembly.PrintDirectResponseWindowComposition
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.DatumRowAggregation
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.ResponseAttainabilityPricing
import HCPoly.Provider.Recurrence.AdaptedCellDomain
import HCPoly.Provider.Regularity.AffineTransfer
import HCPoly.Provider.Regularity.CorrectorGlobalEquation
import HCPoly.Provider.Regularity.EnlargedMarginDatumRegularity
import HCPoly.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
import Homogenization.Book.Ch01.Theorems.CutoffProduct
import Homogenization.Book.Ch02.Dilation
import Homogenization.Book.Ch02.Theorems.Dilation
import Homogenization.Book.Ch02.Theorems.HomogenizationError.Translation
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Definitions
import Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-!
# Cell-anchored response to physical flux frame

The response estimate is kept with the physical scale of its observation
cube.  The difference between the response order and the consumed order is
then bounded by the outer radius of the Whitney system.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- A cell-anchored response rate retains the observation cube's physical
scale before the response is inserted into the flux price. -/
def CellAnchoredObservationRateBound
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (b : ℝ) (responseBound : system.CellIndex → ℝ)
    (epsilon Xval kappaRate Kanchor : ℝ) : Prop :=
  0 ≤ Kanchor ∧ ∀ i,
    0 ≤ responseBound i ∧
      printCellScaleFactor (ruledObservationCube system i) b *
          responseBound i ≤
        Kanchor * (epsilon * Xval) ^ kappaRate

private theorem physicalScale_mul_eq_anchorScale_mul_gap
    [NeZero d] {U : Set (Vec d)} {rho Rad b r : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    physicalDualBesovScaleFactor
          (whitneyCellCube system i) r =
      Real.rpow (3 : ℝ) (-b) *
        Real.rpow (3 : ℝ)
          ((r - b) * ((system.scale i : ℤ) : ℝ)) *
        printCellScaleFactor (ruledObservationCube system i) b := by
  rw [physicalDualBesovScaleFactor_eq_rpow]
  have hcellScale : (whitneyCellCube system i).scale = system.scale i := rfl
  rw [hcellScale]
  unfold printCellScaleFactor
  simp only [ruledObservationCube, originCube]
  rw [show Real.rpow (3 : ℝ) (-b) *
        Real.rpow (3 : ℝ)
          ((r - b) * ((system.scale i : ℤ) : ℝ)) *
        Real.rpow (3 : ℝ)
          (b * (((system.scale i + 1 : ℤ)) : ℝ)) =
      Real.rpow (3 : ℝ)
        (-b + (r - b) * ((system.scale i : ℤ) : ℝ) +
          b * (((system.scale i + 1 : ℤ)) : ℝ)) by
    calc
      _ = Real.rpow (3 : ℝ)
          (-b + (r - b) * ((system.scale i : ℤ) : ℝ)) *
            Real.rpow (3 : ℝ)
              (b * (((system.scale i + 1 : ℤ)) : ℝ)) := by
        exact congrArg
          (fun z : ℝ => z * Real.rpow (3 : ℝ)
            (b * (((system.scale i + 1 : ℤ)) : ℝ)))
          (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
      _ = _ :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm]
  congr 1
  push_cast
  ring

/-- A cell-anchored response rate gives the exact uniform physical flux frame.
Only the order gap and the outer-radius bound are used. -/
theorem physicalFluxEpsilonFrameBound_of_cellAnchoredObservationRate
    [NeZero d] {U : Set (Vec d)} {rho Rad b r Cflux : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpen U) (hRad : 0 ≤ Rad) (hb : 0 < b) (hbr : b < r)
    (hCflux : 0 ≤ Cflux)
    (responseBound : system.CellIndex → ℝ)
    {epsilon Xval kappaRate Kanchor : ℝ}
    (hanchor : CellAnchoredObservationRateBound system b responseBound
      epsilon Xval kappaRate Kanchor) :
    PhysicalFluxEpsilonFrameBound system b r Cflux responseBound
      epsilon Xval kappaRate
        (Real.rpow (3 : ℝ) (-b) * Real.rpow (2 * Rad) (r - b) *
          Cflux * r⁻¹ *
          Book.Ch03.constantCoeffMatrixNormHalf
            (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r * Kanchor) := by
  let Kframe : ℝ :=
    Real.rpow (3 : ℝ) (-b) * Real.rpow (2 * Rad) (r - b) *
      Cflux * r⁻¹ *
      Book.Ch03.constantCoeffMatrixNormHalf
        (identityConstantCoeffMatrix d) *
      responseOneFromTwoGapFactor b r * Kanchor
  have hr : 0 < r := hb.trans hbr
  have hgap : 0 ≤ r - b := (sub_pos.mpr hbr).le
  have hradBase : 0 ≤ 2 * Rad := by positivity
  have hKframe : 0 ≤ Kframe := by
    dsimp only [Kframe]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                (Real.rpow_nonneg hradBase _)) hCflux)
              (inv_nonneg.mpr hr.le))
            (Real.rpow_nonneg (Book.Ch02.matrixNorm_nonneg _) _))
          (responseOneFromTwoGapFactor_nonneg hb hbr))
      hanchor.1
  refine ⟨hKframe, ?_⟩
  intro i
  have hcellSide : (3 : ℝ) ^ system.scale i ≤ 2 * Rad :=
    (ruledCellScale_lt_two_mul_Rad hRad system hU i).le
  have hcellPos : 0 < (3 : ℝ) ^ system.scale i := by positivity
  have hgapScale :
      Real.rpow (3 : ℝ)
          ((r - b) * ((system.scale i : ℤ) : ℝ)) ≤
        Real.rpow (2 * Rad) (r - b) := by
    have hrewrite : Real.rpow (3 : ℝ)
        (((system.scale i : ℤ) : ℝ) * (r - b)) =
        Real.rpow ((3 : ℝ) ^ system.scale i) (r - b) := by
      rw [← Real.rpow_intCast]
      exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
    rw [show (r - b) * ((system.scale i : ℤ) : ℝ) =
      ((system.scale i : ℤ) : ℝ) * (r - b) by ring, hrewrite]
    exact Real.rpow_le_rpow hcellPos.le hcellSide hgap
  have hfront0 : 0 ≤
      Real.rpow (3 : ℝ) (-b) *
        Real.rpow (3 : ℝ)
          ((r - b) * ((system.scale i : ℤ) : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by norm_num) _)
  have hcoefficient0 : 0 ≤ ruledPhysicalFluxResponseCoefficient
      system b r Cflux responseBound i := by
    unfold ruledPhysicalFluxResponseCoefficient
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (physicalDualBesovScaleFactor_nonneg _ _)
              hCflux)
            (inv_nonneg.mpr hr.le))
          (Real.rpow_nonneg (Book.Ch02.matrixNorm_nonneg _) _))
        (responseOneFromTwoGapFactor_nonneg hb hbr))
      (hanchor.2 i).1
  refine ⟨hcoefficient0, ?_⟩
  rw [show ruledPhysicalFluxResponseCoefficient system b r Cflux
      responseBound i =
      (Real.rpow (3 : ℝ) (-b) *
          Real.rpow (3 : ℝ)
            ((r - b) * ((system.scale i : ℤ) : ℝ))) *
        (Cflux * r⁻¹ *
          Book.Ch03.constantCoeffMatrixNormHalf
            (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r) *
        (printCellScaleFactor (ruledObservationCube system i) b *
          responseBound i) by
    unfold ruledPhysicalFluxResponseCoefficient
    rw [physicalScale_mul_eq_anchorScale_mul_gap system i]
    ring]
  have hfront :
      Real.rpow (3 : ℝ) (-b) *
          Real.rpow (3 : ℝ)
            ((r - b) * ((system.scale i : ℤ) : ℝ)) ≤
        Real.rpow (3 : ℝ) (-b) * Real.rpow (2 * Rad) (r - b) :=
    mul_le_mul_of_nonneg_left hgapScale (Real.rpow_nonneg (by norm_num) _)
  have hprice0 : 0 ≤ Cflux * r⁻¹ *
      Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
        responseOneFromTwoGapFactor b r := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hCflux (inv_nonneg.mpr hr.le))
        (Real.rpow_nonneg (Book.Ch02.matrixNorm_nonneg _) _))
      (responseOneFromTwoGapFactor_nonneg hb hbr)
  calc
    _ ≤ (Real.rpow (3 : ℝ) (-b) * Real.rpow (2 * Rad) (r - b)) *
        (Cflux * r⁻¹ *
          Book.Ch03.constantCoeffMatrixNormHalf
            (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r) *
        (printCellScaleFactor (ruledObservationCube system i) b *
          responseBound i) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront hprice0)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hanchor.2 i).1)
    _ ≤ (Real.rpow (3 : ℝ) (-b) * Real.rpow (2 * Rad) (r - b)) *
        (Cflux * r⁻¹ *
          Book.Ch03.constantCoeffMatrixNormHalf
            (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r) *
        (Kanchor * (epsilon * Xval) ^ kappaRate) :=
      mul_le_mul_of_nonneg_left (hanchor.2 i).2
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg hradBase _)) hprice0)
    _ = Kframe * (epsilon * Xval) ^ kappaRate := by
      dsimp only [Kframe]
      ring
end

end RowSupply
end HighContrast
end Homogenization
