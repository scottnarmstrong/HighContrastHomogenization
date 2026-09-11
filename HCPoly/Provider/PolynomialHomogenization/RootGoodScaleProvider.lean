/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.NormalizedReferenceGoodTail

/-!
# The normalized reference certificate at the root scale

The deterministic root reads one sample certificate.  It consists of a
globally compatible normalized reference family and a summable scalar identity
weak-error tail.  The finite geometric enlargement is recorded in the natural
start index of that tail, leaving the real quenched scale unchanged.
-/

namespace Homogenization
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- A sample admits one normalized reference family whose scalar identity
errors have a summable tail above a finite enlargement of the given scale. -/
def NormalizedReferenceGoodScale [NeZero d] (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) : Prop :=
  ∃ (hS : (symmPart abar).PosDef) (s tolerance : ℝ)
      (aRef : Book.Ch03.CoeffFamily d) (L : ℕ),
    0 < s ∧ s < 1 / 2 ∧
    (∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1) ∧
    ScalarIdentityGoodTail aRef s tolerance
      ((Quenched.triadicCeilingIndex x + L : ℕ) : ℤ)

end

end HighContrast
end Homogenization
