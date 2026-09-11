/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.CoarseSchurBridge
import HCPoly.Provider.PolynomialHomogenization.AffineCoeffFamily
import HCPoly.Provider.Response.DomainBridge

/-!
# Reference-cube coefficients for an adapted response

A coefficient from the physical coefficient space is globally measurable and
locally uniformly elliptic.  Pulling it back by the adapted grid gives a
compatible coefficient family on all reference cubes and, in particular, a
coefficient object on the centered cube corresponding to the physical adapted
domain.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ} {q : Mat d}

/-- An adapted physical coefficient produces one compatible affine-pullback
coefficient family on the reference triadic cubes. -/
theorem exists_adaptedReferenceCoeffFamily (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) :
    ∃ aRef : Book.Ch03.CoeffFamily d,
      ∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField =
          affineCoefficient q
            ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
            (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField := by
  obtain ⟨aRef, hRef⟩ := exists_affineCoeffFamily q
    ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
    a.1.aestronglyMeasurable a.2
  refine ⟨aRef, fun Q => ?_⟩
  simpa only [CoeffSpace.coeffOn_toCoeffField] using hRef Q

/-- The compatible affine family supplies the coefficient object on the
centered reference cube associated with an adapted response domain. -/
theorem exists_adaptedReferenceCoeffOn (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) :
    ∃ aRef : Book.Ch02.CoeffOn
        (Book.Ch02.cubeDomain (originCube d t)),
      aRef.toCoeffField =
        affineCoefficient q
          ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
          (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField := by
  obtain ⟨aFamily, hFamily⟩ :=
    exists_adaptedReferenceCoeffFamily hq t a
  exact ⟨aFamily.coeffOn (originCube d t), hFamily (originCube d t)⟩

end

end HighContrast
end Homogenization
