/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.CenteredCubeEuclideanHsAddition
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.DirichletBridge

/-!
# Difference stability for identity Dirichlet regularity

This module packages negation and subtraction on physical centered-cube
Euclidean `L2` fields, then applies identity Dirichlet regularity to the
difference of two weak solutions. Neither solution gradient is assumed to
belong to the positive fractional carrier.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- Pointwise negation, packaged as a centered-cube Euclidean `L2` field. -/
noncomputable def centeredCubeEuclideanL2FieldNeg
    (F : CenteredCubeEuclideanL2Field d m) :
    CenteredCubeEuclideanL2Field d m where
  toField := fun x ↦ -F x
  euclideanMemL2 := by
    have h := F.euclideanMemL2.neg
    convert h using 1
    · rfl
    · funext x
      simp only [Pi.neg_apply, ← HilbertVec.ofVecL_apply]
      exact (HilbertVec.ofVecL d).map_neg _

@[simp] theorem centeredCubeEuclideanL2FieldNeg_apply
    (F : CenteredCubeEuclideanL2Field d m) (x : Vec d) :
    centeredCubeEuclideanL2FieldNeg F x = -F x :=
  rfl

/-- Pointwise subtraction, packaged through addition and negation on the
centered-cube Euclidean `L2` carrier. -/
noncomputable def centeredCubeEuclideanL2FieldSub
    (F G : CenteredCubeEuclideanL2Field d m) :
    CenteredCubeEuclideanL2Field d m :=
  centeredCubeEuclideanL2FieldAdd F (centeredCubeEuclideanL2FieldNeg G)

@[simp] theorem centeredCubeEuclideanL2FieldSub_apply
    (F G : CenteredCubeEuclideanL2Field d m) (x : Vec d) :
    centeredCubeEuclideanL2FieldSub F G x = F x - G x := by
  simp only [centeredCubeEuclideanL2FieldSub,
    centeredCubeEuclideanL2FieldAdd_apply,
    centeredCubeEuclideanL2FieldNeg_apply, sub_eq_add_neg]

end

end HighContrast
end Homogenization
