/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.OrderDecoupledRoundedApplication
import HCPoly.Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

/-!
# Boundary of the order-decoupled rounded interface

The deterministic response is selected before the stochastic exponent.  This
module records the joint interface and the strict direction between its two
orders.  In particular, the printed-order row cannot be read as a row at the
private response order without an additional theorem.
-/

namespace Homogenization
namespace HighContrast
open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-- The printed coefficient application together with the fixed deterministic
response provider.  No equality between their fractional orders is retained. -/
structure OrderDecoupledRoundedResponseJoin
    (d : ℕ) [NeZero d] (g : ℝ) (a : CoeffSpace d) (abar : Mat d)
    (sourceAmplitude target kappa : ℝ) (X : CoeffSpace d → ℝ) where
  application : PrintOrderRoundedCoefficientApplication
    d g a abar sourceAmplitude target kappa X
  responseSpine : PrivateRoundedPhysicalDirichletSpine d
  responseSpine_eq : responseSpine = privateRoundedPhysicalDirichletSpine d
  privateOrder_lt_printOrder :
    responseSpine.order.1 < printCertificateOrder g

/-- The private order is strictly below every admissible printed order. -/
theorem privateRoundedOrder_lt_printCertificateOrder
    (d : ℕ) [NeZero d] {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    (privateRoundedPhysicalDirichletSpine d).order.1 <
      printCertificateOrder g := by
  have hPrivate :=
    (privateRoundedPhysicalDirichletSpine d).order_lt_one_twelfth
  have hg0 : 0 ≤ g := hg.1
  dsimp only [printCertificateOrder]
  linarith only [hPrivate, hg0]

end

end HighContrast
end Homogenization
