/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CenteredCubeEuclideanHsConstantMatrix

/-!
# Addition on the physical centered-cube Euclidean Hs carrier

This module packages pointwise addition on the proof-carrying physical
Euclidean `L2` carrier.  The elementary squared triangle estimate gives a
dimension-free bound for the literal centered-cube Gagliardo energy, and hence
addition preserves `MemCenteredCubeEuclideanHs`.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- Pointwise addition, packaged as a centered-cube Euclidean `L2` field. -/
noncomputable def centeredCubeEuclideanL2FieldAdd
    (F G : CenteredCubeEuclideanL2Field d m) :
    CenteredCubeEuclideanL2Field d m where
  toField := fun x ↦ F x + G x
  euclideanMemL2 := by
    have h := F.euclideanMemL2.add G.euclideanMemL2
    convert h using 1

@[simp] theorem centeredCubeEuclideanL2FieldAdd_apply
    (F G : CenteredCubeEuclideanL2Field d m) (x : Vec d) :
    centeredCubeEuclideanL2FieldAdd F G x = F x + G x :=
  rfl

end

end HighContrast
end Homogenization
