/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra
import HCPoly.Provider.Regularity.AffineTransfer
import HCPoly.Analytic.H1a0ToH10
import HCPoly.Provider.PolynomialHomogenization.AffineCoeffFamily
import HCPoly.Analytic.AffineNegSobolevNorm
import HCPoly.Provider.Initialization.IdentityGrid
import HCPoly.Analytic.AffineH10
import HCPoly.Provider.Recurrence.AdaptedCellDomain
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootCoefficient
import HCPoly.Provider.Regularity.CorrectorGlobalEquation
import HCPoly.Provider.PolynomialHomogenization.RuledLocalizationAssembly
import HCPoly.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
import HCPoly.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.ResponseAttainabilityPricing
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.RealScaleTriadicBracket
import Homogenization.Book.Ch02.Theorems.Dilation
import Homogenization.Book.Ch02.Theorems.HomogenizationError.Translation
import Homogenization.Book.Ch01.Theorems.CutoffProduct
import Homogenization.Deterministic.WeakNormInterfaces.AECongruence
import HCPoly.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.DatumRowAggregation
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.CenteredIndicatorExtensionBasic
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Definitions
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
import Homogenization.Book.Ch02.Dilation
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.PrintDirectGradientResponsePrice
import HCPoly.Provider.PolynomialHomogenization.RuledPairingAggregation
import HCPoly.Provider.Regularity.EnlargedMarginDatumRegularity

/-!
# Direct-gradient composition at the response window, across its two interfaces

Two constraints fix the response order `b`.  The supply side needs
`b > (1 + 3 * g) / 8`: its all-depth series has depth exponent `ρ - 2 * b` with
`ρ = (1 + 3 * g) / 4`, which is nonnegative, hence divergent, at `(1 + g) / 8`.
The conversion side needs `b < (1 + g) / 4`, because `s₀` ranges over
`Set.Ico ((1 + g) / 4) (1 / 2)` and the strict gap must hold at the left endpoint.

The window `((1 + 3 * g) / 8, (1 + g) / 4)` is nonempty exactly when `g < 1`.
Its midpoint `responseWindowOrder g = (3 + 5 * g) / 16` lies strictly inside by
`responseWindowOrder_mem`, and `responseWindowOrder_lt_exponent` supplies the strict
gap against the exponent; both margins equal `(1 - g) / 16`.  The composition is
stated parametrically in `b` through `responseWindow_pos` and
`responseWindow_lt_exponent`, so a change of order is a change of witness.

## The order cannot be lowered

`HomogenizationErrorOnCube Q s .infinity (.finite q)` sums
`geometricWeight s q l * scaleResponseAtScale Q (Q.scale - l) … ^ q` over the depth
`l`, with `geometricWeight s q l = geometricDiscount s q * 3 ^ (-s * q * l)` and
`geometricDiscount s q = 1 - 3 ^ (-s * q)`.  The response factors carry no `s`, so
all of the order dependence sits in the weight, whose ratio `3 ^ (-s * q)` increases
towards `1` as `s` decreases: lowering the order moves mass onto deeper scales.

Passing from an order `B` to a smaller order `b` multiplies the term at depth `l` by
`3 ^ ((B - b) * q * l)`, which is at least one and unbounded in `l`.  No constant
multiple bounds the smaller-order tail by the larger-order one, with or without a
side condition on the ratio; in particular a bound at `(1 + g) / 4` does not transfer
to `(1 + g) / 8`.  The supply is therefore consumed at the order at which it is
delivered, and the window above is the only freedom available.

## Why the interface premises are stated at their four cap values

A provider premise quantified over every value of a cap in `ℝ≥0∞` is vacuous: at the
top element the finiteness conjunct of the joined cap is false, so the premise is
unsatisfiable and the implication it guards has no content.  The premises below are
therefore stated at the four cap values the composition uses, written out.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-! ## The window, once -/

/-- Any order above the supply-side threshold is positive. -/
theorem responseWindow_pos {g b : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hbLow : (1 + 3 * g) / 8 < b) : 0 < b := by
  linarith only [hg.1, hbLow]

/-- **The window gap.**  Any order below `(1+g)/4` is strictly below every
admissible localization exponent, endpoint included. -/
theorem responseWindow_lt_exponent {g b s : ℝ}
    (hbHigh : b < (1 + g) / 4)
    (hs : s ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ)) : b < s :=
  lt_of_lt_of_le hbHigh hs.1

/-! ## The witness inside the window -/

/-- The witness: the midpoint of the window. -/
def responseWindowOrder (g : ℝ) : ℝ := (3 + 5 * g) / 16

theorem responseWindowOrder_mem {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    (1 + 3 * g) / 8 < responseWindowOrder g ∧
      responseWindowOrder g < (1 + g) / 4 := by
  unfold responseWindowOrder
  constructor <;> linarith only [hg.2]

theorem responseWindowOrder_lt_exponent {g s : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hs : s ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ)) :
    responseWindowOrder g < s :=
  responseWindow_lt_exponent (responseWindowOrder_mem hg).2 hs

/-! ## The cap and rate surfaces -/

/-! ## The composition, parametric -/

end

end RowSupply
end HighContrast
end Homogenization
