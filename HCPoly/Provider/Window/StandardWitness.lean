/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.StoppedScale
import HCPoly.Provider.Window.CellGeometry
import HCPoly.Provider.Transport.WindowCellBounds

/-!
# The stopped multiplier on standard cells

At the stopped parent generation the strict successor gives the improved
discount.  Splitting the additional generation from the positive-part exponent
produces the common stopped multiplier, simultaneously for the primal response
and its sharp adjoint.
-/

namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

private theorem stoppedCoefficient_le {g : ℝ} (hg : 0 ≤ g) (E : BlockMat d)
    (jStar M k : ℤ) (a : CoeffSpace d) :
    (3 : ℝ) ^
        (g * max (((M + (windowScaleOffset g E jStar M a : ℤ) : ℤ) : ℝ) -
          ((M : ℝ) - (jStar : ℝ)) - (k : ℝ)) 0) ≤
      windowMultiplier g E jStar M a * burnDiscount g jStar k := by
  set ℓ : ℝ := (windowScaleOffset g E jStar M a : ℝ) with hℓ
  set x : ℝ := (jStar : ℝ) - (k : ℝ) with hx
  have hℓ₀ : 0 ≤ ℓ := by simp [hℓ]
  have hmax : max (x + ℓ) 0 ≤ ℓ + max x 0 := by
    refine max_le ?_ (add_nonneg hℓ₀ (le_max_right x 0))
    calc
      x + ℓ ≤ max x 0 + ℓ := add_le_add_left (le_max_left x 0) ℓ
      _ = ℓ + max x 0 := add_comm _ _
  have hexp : g * max (x + ℓ) 0 ≤ g * (ℓ + max x 0) :=
    mul_le_mul_of_nonneg_left hmax hg
  have hpow : (3 : ℝ) ^ (g * max (x + ℓ) 0) ≤
      (3 : ℝ) ^ (g * (ℓ + max x 0)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    (3 : ℝ) ^
        (g * max (((M + (windowScaleOffset g E jStar M a : ℤ) : ℤ) : ℝ) -
          ((M : ℝ) - (jStar : ℝ)) - (k : ℝ)) 0)
        = (3 : ℝ) ^ (g * max (x + ℓ) 0) := by
            congr 2
            simp only [Int.cast_add, Int.cast_natCast]
            rw [← hℓ, hx]
            ring_nf
    _ ≤ (3 : ℝ) ^ (g * (ℓ + max x 0)) := hpow
    _ = windowMultiplier g E jStar M a * burnDiscount g jStar k := by
      rw [mul_add, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      simp only [windowMultiplier, burnDiscount]
      rw [hℓ, hx]

private theorem blockScale_mono {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    BlockMatLoewnerLE (blockScale c₁ E) (blockScale c₂ E) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale, toFullBlockMat_blockScale]
  refine Matrix.le_iff.mpr ?_
  have hps := (posDef_toFullBlockMat hE hEpd).posSemidef.smul (sub_nonneg.mpr hc)
  simpa [sub_smul] using hps

/-- On every sample with a finite stopped threshold, the stopped multiplier
dominates all standard cells in the original window. -/
theorem standard_primal_of_finite_successor {P : MeasureTheory.Measure (CoeffSpace d)}
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hd : 0 < d) (hg : 0 ≤ g)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} {a : CoeffSpace d}
    (hfinite : ∃ ℓ : ℕ, successorScale g E (M - jStar) a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))) :
    ∀ (k : ℤ) (w : Fin d → ℤ), standardCell d k w ⊆ centeredCube d M →
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (blockScale (windowMultiplier g E jStar M a * burnDiscount g jStar k) E) := by
  intro k w hsub
  obtain ⟨hk, hw⟩ := standardCell_data_in_enlargedWindow hd hsub
    (windowScaleOffset g E jStar M a)
  have hbase := improved_discount_of_successorScale_le hdag
    (successorScale_le_stoppedThreshold hfinite) k hk w hw
  exact hbase.trans (blockScale_mono hdag.refBlock_isSymm hdag.refBlock_posDef
    (stoppedCoefficient_le hg E jStar M k a))

/-- The sharp-adjoint standard-cell bound is the reflection of the primal
bound and carries the same stopped multiplier. -/
theorem standard_adjoint_of_finite_successor {P : MeasureTheory.Measure (CoeffSpace d)}
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hd : 0 < d) (hg : 0 ≤ g)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} {a : CoeffSpace d}
    (hfinite : ∃ ℓ : ℕ, successorScale g E (M - jStar) a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))) :
    ∀ (k : ℤ) (w : Fin d → ℤ), standardCell d k w ⊆ centeredCube d M →
      BlockMatLoewnerLE (coarseStarInv (standardCell d k w) a)
        (blockScale (windowMultiplier g E jStar M a * burnDiscount g jStar k)
          (blockReflect E)) := by
  intro k w hsub
  have hprimal := standard_primal_of_finite_successor hd hg hdag hfinite k w hsub
  simpa only [Transport.coarseStarInv_eq_blockReflect, Transport.blockScale_blockReflect] using
    Transport.blockMatLoewnerLE_blockReflect hprimal

/-- Almost-sure finiteness of the strict successor supplies both standard-cell
rows simultaneously throughout the original window. -/
theorem ae_standard_rows_of_successor_ne_top
    {P : MeasureTheory.Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hd : 0 < d) (hg : 0 ≤ g)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ}
    (hfinite : ∀ᵐ a ∂P, successorScale g E (M - jStar) a ≠ ⊤) :
    ∀ᵐ a ∂P, ∀ (k : ℤ) (w : Fin d → ℤ),
      standardCell d k w ⊆ centeredCube d M →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
            (blockScale (windowMultiplier g E jStar M a * burnDiscount g jStar k) E) ∧
          BlockMatLoewnerLE (coarseStarInv (standardCell d k w) a)
            (blockScale (windowMultiplier g E jStar M a * burnDiscount g jStar k)
              (blockReflect E)) := by
  filter_upwards [hfinite] with a ha
  have hthreshold := exists_stoppedThreshold_of_ne_top ha
  intro k w hsub
  exact ⟨standard_primal_of_finite_successor hd hg hdag hthreshold k w hsub,
    standard_adjoint_of_finite_successor hd hg hdag hthreshold k w hsub⟩

end

end Window
end HighContrast
end Homogenization
