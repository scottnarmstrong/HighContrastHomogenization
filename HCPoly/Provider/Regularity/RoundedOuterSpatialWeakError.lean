/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CommonQuantitativeAffineCertificate
import HCPoly.Provider.Regularity.RoundedOuterSpatialResponseCommonScale
import HCPoly.Provider.Response.WeakNorm

/-!
# Rounded outer spatial weak errors

The rounded spatial response row is written with the canonical aligned index
set and then square-rooted.  A quantitative normalized reference certificate
controls this physical weak error at the common affine scale.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The scalar weak error on one base-rounded outer cell, including the full
depth sum and the spatial maximum over every aligned cell at each depth. -/
noncomputable def baseRoundedSpatialWeakError [NeZero d]
    (a : CoeffSpace d) (abar : Mat d)
    (_hS : (symmPart abar).PosDef) (s : ℝ) (M : ℤ) : ℝ :=
  Real.sqrt (∑' l : ℕ,
    Book.Ch02.geometricWeight s 2 l *
      Book.Ch02.finsetSupReal
        (Response.alignedIndex (baseRoundedGrid (symmPart abar))
          (M - (l : ℤ)) M)
        (fun w ↦
          baseRoundedNormalizedDoubledResponseMaxAt
            a abar _hS (M - (l : ℤ)) w))

end

end Transport

noncomputable section

variable {d : ℕ}

/-- Targeting the quantitative certificate supplies the same reference family
with its characterization rewritten on the adapted local coefficient carrier.
No compatibility assumption is added to the certificate. -/
theorem QuantitativeNormalizedReferenceCertificate.exists_targetedRoundedReferenceCoeffFamily
    [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    {s sourceAmplitude target kappa : ℝ} {X : CoeffSpace d → ℝ}
    (h : QuantitativeNormalizedReferenceCertificate
      abar s sourceAmplitude kappa (X a) a)
    (hTarget : 0 < target) (t : ℤ) :
    ∃ (hS : (symmPart abar).PosDef) (aRef : Book.Ch03.CoeffFamily d),
      0 < s ∧ s < 1 / 4 ∧ 0 ≤ target ∧ 0 < kappa ∧ 1 ≤ X a ∧
      (∀ R : TriadicCube d,
        (aRef.coeffOn R).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ((normalizedCenteredCoeff a abar hS).coeffOn
              (Response.adaptedDomain
                (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField) ∧
      ScalarIdentityPowerTail aRef s target kappa
        (targetedQuantitativeEffectiveScale
          sourceAmplitude target kappa X a) := by
  have hTargeted := h.targetedEffectiveScale hTarget
  obtain ⟨hS, aRef, hs, hsLt, hTargetNonneg, hKappa, _, haRef, hTail⟩ :=
    hTargeted
  obtain ⟨_, _, _, _, _, _, hX, _, _⟩ := h
  refine ⟨hS, aRef, hs, hsLt, hTargetNonneg, hKappa, hX, ?_, hTail⟩
  intro R
  simpa only [CoeffSpace.coeffOn_toCoeffField] using haRef R

end

end HighContrast
end Homogenization
