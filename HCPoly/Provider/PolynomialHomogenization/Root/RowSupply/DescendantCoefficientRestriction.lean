/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Homogenization.Book.Ch02.MultiscaleEllipticity

/-!
# Descendant restriction of a root coefficient identification

The compatibility field of a triadic coefficient family transports an a.e.
identification on a root cube to every descendant cube.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open MeasureTheory

variable {d : ℕ}

/-- A root-cube coefficient identification restricts to every descendant,
using the a.e. compatibility built into `TriadicCoeffFamily`. -/
theorem coeffOn_descendant_ae_eq_of_root_ae_eq
    (a : Book.Ch02.TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k)
    {f : Vec d → Mat d}
    (hroot : (a.coeffOn Q).toCoeffField =ᵐ[
      volumeMeasureOn (openCubeSet Q)] f) :
    (a.coeffOn R).toCoeffField =ᵐ[
      volumeMeasureOn (openCubeSet R)] f := by
  have hRdepth : R ∈ descendantsAtDepth Q (Q.scale - k).toNat := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
    exact hR
  have hsubset : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hRdepth
  have hmeasure : volumeMeasureOn (openCubeSet R) ≤
      volumeMeasureOn (openCubeSet Q) := by
    simpa only [volumeMeasureOn] using
      Measure.restrict_mono_set volume hsubset
  have hparent : (a.coeffOn Q).toCoeffField =ᵐ[
      volumeMeasureOn (openCubeSet R)] f :=
    hroot.filter_mono (ae_mono hmeasure)
  have hchild : (a.coeffOn R).toCoeffField =ᵐ[
      volumeMeasureOn (openCubeSet R)]
        (a.coeffOn Q).toCoeffField :=
    a.restrictsTo_descendant hk hR
  exact hchild.trans hparent

end RowSupply
end HighContrast
end Homogenization
