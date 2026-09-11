/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Homogenization.Geometry.Translation
import Homogenization.Sobolev.WeakDerivatives

/-!
# Translation of weak-gradient pairs

The upstream `H1Function` translation API contains this change of variables
for bundled square-integrable functions.  Corrector representatives are used
globally and locally, so this file proves the underlying predicate-level
transport without adding an `H1Function` witness.
-/

namespace Homogenization
namespace HighContrast

noncomputable section

open MeasureTheory

/-- Pulling a weak-gradient pair on `U + z` back by `x ↦ x + z` gives a
weak-gradient pair on `U`. -/
theorem HasWeakGradientOn.untranslate {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (z : Vec d) (h : HasWeakGradientOn (translateSet z U) u Du) :
    HasWeakGradientOn U (fun x => u (x + z)) (fun x => Du (x + z)) := by
  intro i phi hphi hphiCompact hphiSupport
  let psi : Vec d → ℝ := fun x => phi (x - z)
  have hpsiSmooth : ContDiff ℝ (⊤ : ℕ∞) psi := by
    simpa only [psi] using
      hphi.comp (contDiff_id.sub contDiff_const)
  have hpsiCompact : HasCompactSupport psi := by
    show HasCompactSupport (phi ∘ Homeomorph.subRight z)
    simpa only [psi, Function.comp_apply] using
      hphiCompact.comp_homeomorph (Homeomorph.subRight z)
  have hpsiSupport : tsupport psi ⊆ translateSet z U := by
    intro x hx
    have hx' : x - z ∈ tsupport phi := by
      rw [show psi = phi ∘ Homeomorph.subRight z by rfl,
        tsupport_comp_eq_preimage phi (Homeomorph.subRight z)] at hx
      exact hx
    exact mem_translateSet_iff_sub_mem.mpr (hphiSupport hx')
  have hweak := h i psi hpsiSmooth hpsiCompact hpsiSupport
  have hmain :
      ∫ x in translateSet z U,
          u x * (fderiv ℝ phi (x - z)) (basisVec i) ∂volume =
        -∫ x in translateSet z U, Du x i * phi (x - z) ∂volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ phi (x - z)) (basisVec i)) =
          fun x => u x * (fderiv ℝ psi x) (basisVec i) := by
      funext x
      have hderiv :
          fderiv ℝ (fun y : Vec d => phi (y - z)) x =
            fderiv ℝ phi (x - z) := by
        exact fderiv_comp_sub (𝕜 := ℝ) (f := phi) (x := x) z
      rw [show psi = fun y : Vec d => phi (y - z) by rfl, hderiv]
    calc
      ∫ x in translateSet z U,
          u x * (fderiv ℝ phi (x - z)) (basisVec i) ∂volume =
          ∫ x in translateSet z U,
            u x * (fderiv ℝ psi x) (basisVec i) ∂volume := by rw [hfun]
      _ = -∫ x in translateSet z U, Du x i * psi x ∂volume := hweak
      _ = -∫ x in translateSet z U, Du x i * phi (x - z) ∂volume := by
        rfl
  have hchangeLeft :
      ∫ x in U,
          u (x + z) * (fderiv ℝ phi x) (basisVec i) ∂volume =
        ∫ x in translateSet z U,
          u x * (fderiv ℝ phi (x - z)) (basisVec i) ∂volume := by
    simpa only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => u x * (fderiv ℝ phi (x - z)) (basisVec i)))
  have hchangeRight :
      ∫ x in translateSet z U, Du x i * phi (x - z) ∂volume =
        ∫ x in U, Du (x + z) i * phi x ∂volume := by
    simpa only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => Du x i * phi (x - z))).symm
  calc
    ∫ x in U, u (x + z) * (fderiv ℝ phi x) (basisVec i) ∂volume =
        ∫ x in translateSet z U,
          u x * (fderiv ℝ phi (x - z)) (basisVec i) ∂volume := hchangeLeft
    _ = -∫ x in translateSet z U, Du x i * phi (x - z) ∂volume := hmain
    _ = -∫ x in U, Du (x + z) i * phi x ∂volume := by rw [hchangeRight]

end

end HighContrast
end Homogenization
