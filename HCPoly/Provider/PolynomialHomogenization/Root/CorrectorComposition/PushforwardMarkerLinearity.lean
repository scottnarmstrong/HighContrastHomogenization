/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.PushforwardCorrectorFamily
import HCPoly.Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificatePositiveDefiniteness

/-!
# The corrector side recomposed at the pushforward marker

`RootInterface.polynomial_homogenization_of_quenched_scale_v2` is instantiated at

* `GoodScale   := reconciledRootGoodScale d cStar`   (the ceiling-exporting smallness interface),
* `CorrectorFamily := Root.RootPushCorrectorFamilyPredicate d`  (the
  pushforward marker).

`hhomogenized` is already proved.  This module discharges
the stationary corrector family clause from the stationary corrector family clause's `correctorFamilyHole_of_normalizedSupply`, and
supplies the slope linearity that the large-scale C¹ slope approximation clause needs from the marker itself, so that no
clause of the corrector side is left as a bare assumption about the family.
-/

namespace Homogenization
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

/-- Slope linearity holds for **every** pair carrying the pushforward marker,
not just for the one the hole returns: the marker is the definitional record. -/
theorem pushforwardMarker_linear (d : ℕ) [NeZero d] :
    ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
      (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
      Root.RootPushCorrectorFamilyPredicate d abar Phi gradPhi →
      ∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
        gradPhi (c • e + e') a =ᵐ[volume]
          fun y ↦ c • gradPhi e a y + gradPhi e' a y := by
  rintro abar Phi gradPhi ⟨hS, rfl, rfl⟩ c e e' a
  exact Root.pushforwardPhysicalGradPhi_linear d abar hS c e e' a

end

end CorrectorComposition
end HighContrast
end Homogenization
