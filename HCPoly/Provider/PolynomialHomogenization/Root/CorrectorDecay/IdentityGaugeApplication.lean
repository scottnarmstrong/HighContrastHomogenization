/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityGaugeSpecialization
import HCPoly.Provider.Regularity.PrintOrderIdentityCubeDualRegularity

namespace Homogenization
namespace HighContrast

open Set

noncomputable section

/-- A printed certificate, re-presented on a coefficient family whose
selected rounded geometry is exactly the identity gauge. -/
structure IdentityGaugeApplication
    (d : ℕ) [NeZero d] (g : ℝ) (a : CoeffSpace d) (abar : Mat d)
    (amplitude kappa x : ℝ) where
  Cid : ℝ
  identityRegularity : PrintOrderIdentityCubeDualRegularityWithConstant d g Cid
  spine : PrintOrderToleranceSelectedRoundedSpine d Cid
  hS : (symmPart abar).PosDef
  hI : (symmPart (1 : Mat d)).PosDef
  aIdentity : Book.Ch03.CoeffFamily d
  realizesIdentityGauge : ∀ Q : TriadicCube d,
    (aIdentity.coeffOn Q).toCoeffField =
      (⇑(spine.geometry.centeredCoeffSpace (1 : Mat d) hI
        (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d)
  powerTail : ScalarIdentityPowerTail aIdentity
    (printCertificateOrder g) amplitude kappa x

namespace IdentityGaugeApplication

variable {d : ℕ} [NeZero d] {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
  {amplitude kappa x : ℝ}

def geom (application : IdentityGaugeApplication
    d g a abar amplitude kappa x) : RoundedGenerationAnalyticGeometry d :=
  application.spine.geometry

end IdentityGaugeApplication

end

end HighContrast
end Homogenization
