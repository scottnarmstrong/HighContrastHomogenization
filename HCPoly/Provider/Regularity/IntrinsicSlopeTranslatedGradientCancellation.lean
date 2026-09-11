/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.IntrinsicSlopeTranslatedFullGradientUniqueness

/-!
# Corrector-gradient cancellation after translated slope identification

Once intrinsic normalization identifies the affine slopes in a translated
full-gradient identity, cancellation yields the corresponding identity of the
corrector gradients themselves.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

/-- Intrinsic normalization and one weak corrector row turn a translated global
full-gradient identity into the translated corrector-gradient identity. -/
theorem globalGradient_translate_ae_eq_of_intrinsicSlopes_of_fullGradient_ae_eq_of_weakRow
    {d : ℕ} [NeZero d]
    {e e' : Vec d} {Phi Psi : NormalizedLocalH1Carrier d}
    (he : HasIntrinsicNormalizedSlope e Phi)
    (he' : HasIntrinsicNormalizedSlope e' Psi)
    (t : Vec d) (eRow : Vec d) {s : ℝ} (hs : 0 < s) (hs2 : s < 1 / 2)
    (q0 : ℕ) (N : ℝ)
    (hRow : ∀ q : ℕ, q0 ≤ q →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (q : ℤ)) s
        (fun x ↦ eRow + Phi.globalGradientRepresentative x) ≤ N)
    (hFullGradient : (fun x ↦ e + Phi.globalGradientRepresentative (x + t))
      =ᵐ[volume] fun x ↦ e' + Psi.globalGradientRepresentative x) :
    (fun x ↦ Phi.globalGradientRepresentative (x + t)) =ᵐ[volume]
      Psi.globalGradientRepresentative := by
  have hslope : e = e' :=
    intrinsicSlope_eq_of_translated_globalFullGradient_ae_eq_of_weakRow
      he he' t eRow hs hs2 q0 N hRow hFullGradient
  filter_upwards [hFullGradient] with x hx
  rw [hslope] at hx
  exact add_left_cancel hx

end

end HighContrast
end Homogenization
