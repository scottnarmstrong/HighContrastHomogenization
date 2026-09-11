/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CommonQuantitativeAffineScale
import HCPoly.Provider.Regularity.QuantitativeCorrectorThreshold
import HCPoly.Provider.Regularity.RoundedOuterSpatialResponsePowerTail
import HCPoly.Provider.PolynomialHomogenization.PrintOrderCertificateInhabitation

/-!
# Rate-bearing root event at the printed fractional order

This is the order-31 event surface with the response order selected from the
already fixed `g`.  Its scale, deterministic length, tail, and common-scale
bookkeeping are unchanged.
-/

namespace Homogenization
namespace HighContrast
namespace Certificate

open MeasureTheory Set

noncomputable section

/-- The root-facing rate certificate with its order selected after `g`. -/
def PrintOrderRateBearingCommonAffineGoodScale
    (d : ℕ) [NeZero d] (g c kappaRate : ℝ) (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) : Prop :=
  ∃ (sourceAmplitude : ℝ) (X : CoeffSpace d → ℝ),
    PrintOrderQuantitativeNormalizedReferenceCertificate
        abar g sourceAmplitude kappaRate (X a) a ∧
      x = commonQuantitativeAffineScale sourceAmplitude
        (correctorTargetAmplitude c kappaRate) kappaRate
        (Transport.roundedOuterResponseAffineConstant d)
        (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
        kappaRate X a

end

end Certificate
end HighContrast
end Homogenization
