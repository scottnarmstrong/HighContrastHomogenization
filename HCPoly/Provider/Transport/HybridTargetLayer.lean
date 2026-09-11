/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.HybridTubeGeometry

/-!
# A target layer from nearby exterior points

The packed tiles relevant to the hybrid tube all lie close to an exterior
point of the outer target.  This is the inner boundary-layer estimate in the
form that observation consumes.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Two points of one adapted cell have controlled separation after changing
to the coordinates of a second grid. -/
theorem abs_matVecMul_inv_sub_le_of_mem_adaptedCellAt {p q : Mat d}
    {a : ℤ} {w : Fin d → ℤ} {x z : Vec d}
    (hx : x ∈ adaptedCellAt q a w) (hz : z ∈ adaptedCellAt q a w) (i : Fin d) :
    |matVecMul p⁻¹ (x - z) i| ≤
      ‖p⁻¹ * q‖ * (Real.sqrt d * (3 : ℝ) ^ a) := by
  obtain ⟨x', hx', hx'eq⟩ := (Recurrence.adaptedCellAt_eq_image q a w ▸ hx)
  obtain ⟨z', hz', hz'eq⟩ := (Recurrence.adaptedCellAt_eq_image q a w ▸ hz)
  have hcell : ∀ k, |(x' - z') k| ≤ (3 : ℝ) ^ a := by
    intro k
    rw [Recurrence.mem_standardCell_iff] at hx' hz'
    have h1 := hx' k
    have h2 := hz' k
    rw [Pi.sub_apply, abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have h := abs_matVecMul_le_of_abs_le (p⁻¹ * q) hcell i
  have hdiff : matVecMul p⁻¹ (x - z) = matVecMul (p⁻¹ * q) (x' - z') := by
    have hqdiff : matVecMul q (x' - z') = x - z := by
      simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, hx'eq, hz'eq]
    calc
      matVecMul p⁻¹ (x - z) = matVecMul p⁻¹ (matVecMul q (x' - z')) :=
        congrArg (matVecMul p⁻¹) hqdiff.symm
      _ = matVecMul (p⁻¹ * q) (x' - z') := by rw [matVecMul_mul]
  rwa [← hdiff] at h

/-- A subset of an adapted cell whose every point is coordinatewise close to
some point outside the cell lies in the corresponding inner boundary layer. -/
theorem volume_le_of_close_outside {p : Mat d} (hp : p.PosDef) {j : ℤ}
    {y : Vec d} {A : Set (Vec d)} {t : ℝ} (ht : 0 ≤ t)
    (hAW : A ⊆ adaptedCellTranslate p j y)
    (hclose : ∀ x ∈ A, ∃ z : Vec d, z ∉ adaptedCellTranslate p j y ∧
      ∀ i, |matVecMul p⁻¹ (x - z) i| ≤ t) :
    volume A ≤
      ENNReal.ofReal (2 * (d : ℝ) * t * (3 : ℝ) ^ (-j)) *
        volume (adaptedCellTranslate p j y) := by
  have hdet : IsUnit p.det := (Matrix.isUnit_iff_isUnit_det p).mp hp.isUnit
  have hinv : ∀ w : Vec d, matVecMul p (matVecMul p⁻¹ w) = w := by
    intro w
    show p *ᵥ p⁻¹ *ᵥ w = w
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hsub : A ⊆ (fun z => y + matVecMul p z) ''
      {z : Vec d | z ∈ centeredCube d j ∧
        ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} := by
    intro x hxA
    obtain ⟨xt, hxt, hxeq⟩ := (adaptedCellTranslate_eq_image p j y ▸ hAW hxA)
    obtain ⟨z, hzout, hzx⟩ := hclose x hxA
    set zt : Vec d := matVecMul p⁻¹ (z - y) with hztdef
    have hzeq : y + matVecMul p zt = z := by
      rw [hztdef, hinv]
      abel
    have hztout : zt ∉ centeredCube d j := by
      intro hmem
      exact hzout (adaptedCellTranslate_eq_image p j y ▸ ⟨zt, hmem, hzeq⟩)
    have hpx : matVecMul p xt = x - y := eq_sub_of_add_eq' hxeq
    have hpz : matVecMul p zt = z - y := eq_sub_of_add_eq' hzeq
    have hdiff : xt - zt = matVecMul p⁻¹ (x - z) := by
      have hp1 : matVecMul p (xt - zt) = x - z := by
        rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, hpx, hpz]
        abel
      have hp2 : matVecMul p⁻¹ (matVecMul p (xt - zt)) = xt - zt := by
        show p⁻¹ *ᵥ p *ᵥ (xt - zt) = xt - zt
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
      rw [← hp2, hp1]
    obtain ⟨i, hi⟩ : ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ |zt i| := by
      by_contra hcon
      push_neg at hcon
      refine hztout (Recurrence.mem_centeredCube_iff.mpr fun i => ?_)
      have hii := hcon i
      rw [abs_lt] at hii
      exact ⟨by linarith only [hii.1], hii.2⟩
    refine ⟨xt, ⟨hxt, i, ?_⟩, hxeq⟩
    have hcoord := hzx i
    rw [← hdiff] at hcoord
    change |xt i - zt i| ≤ t at hcoord
    have habs : |zt i| - |xt i| ≤ |xt i - zt i| := by
      rw [abs_sub_comm]
      exact abs_sub_abs_le_abs_sub _ _
    linarith only [hi, hcoord, habs]
  calc
    volume A ≤ volume ((fun z => y + matVecMul p z) ''
        {z : Vec d | z ∈ centeredCube d j ∧
          ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|}) := measure_mono hsub
    _ = ENNReal.ofReal |p.det| * volume
        {z : Vec d | z ∈ centeredCube d j ∧
          ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ j - t ≤ |z i|} :=
      volume_image_affine p y _
    _ ≤ ENNReal.ofReal |p.det| *
        (ENNReal.ofReal (2 * (d : ℝ) * t * (3 : ℝ) ^ (-j)) *
          volume (centeredCube d j)) :=
      mul_le_mul' le_rfl (volume_layer_centeredCube_le j ht)
    _ = ENNReal.ofReal (2 * (d : ℝ) * t * (3 : ℝ) ^ (-j)) *
        volume (adaptedCellTranslate p j y) := by
      rw [adaptedCellTranslate_eq_image, volume_image_affine]
      ring

end

end Transport
end HighContrast
end Homogenization
