/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.Boundary
import HCPoly.Provider.Initialization.Multiplier
import HCPoly.Provider.Initialization.Reference
import HCPoly.Geometry.IntegralOrder
import HCPoly.Provider.Sharp.CoarseBlockPositivity

/-!
# Quantitative initialization of an adapted mean

The pathwise window bound can be averaged because the common multiplier is
integrable.  Its coupled-window moment is at most two, giving the upper mean
comparison.  Applying sharp to that averaged comparison and then using the
annealed sharp order gives the matching lower comparison.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem smul_le_smul_of_scalar_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {s t : ℝ} (hst : s ≤ t) : s • A ≤ t • A := by
  refine Matrix.le_iff.mpr ?_
  rw [← sub_smul]
  exact hA.smul (sub_nonneg.mpr hst)

/-- Averaging the window domination gives the exact upper comparison used in
the initialization anchor. -/
theorem adaptedMean_le_two_boundary_reference
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] [Nonempty (Fin d)]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} (hCd : 1 ≤ Cd) {jStar M : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu : Mat d} (hmu : mu.PosDef) {r : ℤ}
    (hindex : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r 0) :
    BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar mu) r)
      (blockScale (boundaryConst Cd g mu * 2) E) := by
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  have hint := Transport.hasFiniteAdaptedMean_of_isWindowMultiplier
    hY hmu hq hindex.1 hindex.2.2
  have hYint : Integrable Y P := Transport.integrable_of_isWindowMultiplier hY
  have hEYenn : ENNReal.ofReal (∫ a, Y a ∂P) ≤ ENNReal.ofReal 2 := by
    have hbounds := initialization_multiplier_bounds hg hw hY
    exact hbounds.1.trans (by simpa using hbounds.2)
  have hEY : ∫ a, Y a ∂P ≤ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hEYenn
  set B : ℝ := boundaryConst Cd g mu with hB
  have hB1 : 1 ≤ B := by
    rw [hB]
    exact one_le_boundaryConst hCd hg hmu
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hAint : Integrable
      (fun a => toFullBlockMat
        (coarseBlock (adaptedCell (roundedGrid jStar mu) r) a)) P :=
    integrable_toFullBlockMat hint
  have hRint : Integrable
      (fun a => (B * Y a) • toFullBlockMat E) P := by
    refine integrable_of_entries fun i j => ?_
    have hij : Integrable (fun a => (B * Y a) * toFullBlockMat E i j) P :=
      (hYint.const_mul B).mul_const _
    simpa only [Matrix.smul_apply, smul_eq_mul] using hij
  have hmono : toFullBlockMat (adaptedMean P (roundedGrid jStar mu) r) ≤
      ∫ a, (B * Y a) • toFullBlockMat E ∂P := by
    rw [Recurrence.toFullBlockMat_adaptedMean_eq_integral hint]
    refine integral_mono' hAint hRint ?_
    filter_upwards [Transport.ae_blockMatLoewnerLE_coarseBlock_adaptedCell
      hY hmu hindex.1 hindex.2.2] with a ha
    have hflat := le_of_blockMatLoewnerLE
      (isSymmetricBlockMat_coarseBlock _ a)
      (isSymmetricBlockMat_blockScale _ hE) ha
    simpa only [hB, toFullBlockMat_blockScale] using hflat
  have hrhs : (∫ a, (B * Y a) • toFullBlockMat E ∂P) =
      (B * ∫ a, Y a ∂P) • toFullBlockMat E := by
    calc
      (∫ a, (B * Y a) • toFullBlockMat E ∂P) =
          (∫ a, B * Y a ∂P) • toFullBlockMat E :=
            integral_smul_const (𝕜 := ℝ) (μ := P)
              (fun a => B * Y a) (toFullBlockMat E)
      _ = (B * ∫ a, Y a ∂P) • toFullBlockMat E := by
        rw [integral_const_mul]
  rw [hrhs] at hmono
  refine blockMatLoewnerLE_of_le (hmono.trans ?_)
  rw [toFullBlockMat_blockScale, hB]
  exact smul_le_smul_of_scalar_le
    (posDef_toFullBlockMat hE hEpd).posSemidef
    (mul_le_mul_of_nonneg_left hEY hB0)

/-- The exact two-sided adapted-mean comparison in the initialization anchor. -/
theorem adaptedMean_reference_comparison
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] [Nonempty (Fin d)]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} (hCd : 1 ≤ Cd) {jStar M : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu : Mat d} (hmu : mu.PosDef) {r : ℤ}
    (hindex : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r 0) :
    BlockMatLoewnerLE
        (blockScale (boundaryConst Cd g mu * 2)⁻¹ (blockSharp E))
        (adaptedMean P (roundedGrid jStar mu) r) ∧
      BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar mu) r)
        (blockScale (boundaryConst Cd g mu * 2) E) := by
  have hupper := adaptedMean_le_two_boundary_reference hg hE hEpd hCd hw hY hmu hindex
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  have hint := Transport.hasFiniteAdaptedMean_of_isWindowMultiplier
    hY hmu hq hindex.1 hindex.2.2
  have hmeanSymm := Recurrence.isSymmetricBlockMat_adaptedMean
    P (roundedGrid jStar mu) r
  have hmeanPd := Transport.blockPosDef_adaptedMean_of_isWindowMultiplier
    hY hmu hq hindex.1 hindex.2.2
  have hB1 : 1 ≤ boundaryConst Cd g mu := one_le_boundaryConst hCd hg hmu
  have hc : 0 < boundaryConst Cd g mu * 2 :=
    mul_pos (lt_of_lt_of_le zero_lt_one hB1) (by norm_num)
  have hscalePd : Book.Ch02.BlockPosDef
      (blockScale (boundaryConst Cd g mu * 2) E) := by
    apply (blockPosDef_iff_posDef
      (isSymmetricBlockMat_blockScale (boundaryConst Cd g mu * 2) hE)).mpr
    rw [toFullBlockMat_blockScale]
    exact posDef_smul (posDef_toFullBlockMat hE hEpd) hc
  have hsharp := blockMatLoewnerLE_blockSharp_of_le hmeanSymm
    (isSymmetricBlockMat_blockScale _ hE) hmeanPd hscalePd hupper
  rw [blockSharp_blockScale hE hEpd hc] at hsharp
  have hself : BlockMatLoewnerLE
      (blockSharp (adaptedMean P (roundedGrid jStar mu) r))
      (adaptedMean P (roundedGrid jStar mu) r) := by
    simpa only [adaptedMean] using
      (Sharp.blockSharp_annealedBlock_le_of_nonempty
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell
          (Recurrence.posDef_of_isRoundedGrid hq) r)
        (Recurrence.adaptedCell_nonempty (roundedGrid jStar mu) r) hint)
  exact ⟨hsharp.trans hself, hupper⟩

end

end Initialization
end HighContrast
end Homogenization
