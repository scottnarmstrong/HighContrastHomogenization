/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.IdentityGrid
import HCPoly.Provider.Initialization.MeanComparison

/-!
# Mean comparison on the identity grid

Identity-grid cells are standard aligned cubes, so the standard window row
removes the boundary factor from the general adapted-grid comparison.
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

/-- At every identity-grid scale in a coupled window, the adapted mean lies
between one half of the sharp reference and twice the reference. -/
theorem identity_mean_reference_comparison
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] [Nonempty (Fin d)]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M r : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hjr : jStar ≤ r) (hrM : r ≤ M) :
    BlockMatLoewnerLE (blockScale (2 : ℝ)⁻¹ (blockSharp E))
        (adaptedMean P (roundedGrid jStar (1 : Mat d)) r) ∧
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid jStar (1 : Mat d)) r)
        (blockScale 2 E) := by
  have hindex := identity_admissible_index hw hjr hrM
  have hstruct := finite_and_posDef_of_admissible hw hY Matrix.PosDef.one hindex
  have hint := hstruct.1
  have hmeanPd := hstruct.2
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw Matrix.PosDef.one
  have hcell : standardCell d r 0 ⊆ centeredCube d M := by
    rw [standardCell_zero]
    exact centeredCube_subset_centeredCube hrM
  have hpath : ∀ᵐ a ∂P,
      BlockMatLoewnerLE
        (coarseBlock (adaptedCell (roundedGrid jStar (1 : Mat d)) r) a)
        (blockScale (Y a) E) := by
    filter_upwards [hY.standard_primal] with a ha
    have h := ha r 0 hcell
    rw [burnDiscount_eq_one hjr, mul_one] at h
    simpa only [standardCell_zero, roundedGrid_one hw, adaptedCell_one] using h
  have hYint : Integrable Y P := Transport.integrable_of_isWindowMultiplier hY
  have hEYenn : ENNReal.ofReal (∫ a, Y a ∂P) ≤ ENNReal.ofReal 2 := by
    have hbounds := initialization_multiplier_bounds hg hw hY
    exact hbounds.1.trans (by simpa using hbounds.2)
  have hEY : ∫ a, Y a ∂P ≤ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hEYenn
  have hAint : Integrable
      (fun a => toFullBlockMat
        (coarseBlock (adaptedCell (roundedGrid jStar (1 : Mat d)) r) a)) P :=
    integrable_toFullBlockMat hint
  have hRint : Integrable (fun a => Y a • toFullBlockMat E) P := by
    refine integrable_of_entries fun i j => ?_
    have hij : Integrable (fun a => Y a * toFullBlockMat E i j) P :=
      hYint.mul_const _
    simpa only [Matrix.smul_apply, smul_eq_mul] using hij
  have hmono :
      toFullBlockMat (adaptedMean P (roundedGrid jStar (1 : Mat d)) r) ≤
        ∫ a, Y a • toFullBlockMat E ∂P := by
    rw [Recurrence.toFullBlockMat_adaptedMean_eq_integral hint]
    refine integral_mono' hAint hRint ?_
    filter_upwards [hpath] with a ha
    have hflat := le_of_blockMatLoewnerLE
      (isSymmetricBlockMat_coarseBlock _ a)
      (isSymmetricBlockMat_blockScale _ hE) ha
    simpa only [toFullBlockMat_blockScale] using hflat
  have hrhs : (∫ a, Y a • toFullBlockMat E ∂P) =
      (∫ a, Y a ∂P) • toFullBlockMat E :=
    integral_smul_const (𝕜 := ℝ) (μ := P) Y (toFullBlockMat E)
  rw [hrhs] at hmono
  have hupper : BlockMatLoewnerLE
      (adaptedMean P (roundedGrid jStar (1 : Mat d)) r)
      (blockScale 2 E) := by
    refine blockMatLoewnerLE_of_le (hmono.trans ?_)
    rw [toFullBlockMat_blockScale]
    exact smul_le_smul_of_scalar_le
      (posDef_toFullBlockMat hE hEpd).posSemidef hEY
  have hscalePd : Book.Ch02.BlockPosDef (blockScale 2 E) := by
    apply (blockPosDef_iff_posDef
      (isSymmetricBlockMat_blockScale 2 hE)).mpr
    rw [toFullBlockMat_blockScale]
    exact posDef_smul (posDef_toFullBlockMat hE hEpd) (by norm_num)
  have hsharp := blockMatLoewnerLE_blockSharp_of_le
    (Recurrence.isSymmetricBlockMat_adaptedMean
      P (roundedGrid jStar (1 : Mat d)) r)
    (isSymmetricBlockMat_blockScale 2 hE) hmeanPd hscalePd hupper
  rw [blockSharp_blockScale hE hEpd (by norm_num)] at hsharp
  have hself : BlockMatLoewnerLE
      (blockSharp (adaptedMean P (roundedGrid jStar (1 : Mat d)) r))
      (adaptedMean P (roundedGrid jStar (1 : Mat d)) r) := by
    simpa only [adaptedMean] using
      (Sharp.blockSharp_annealedBlock_le_of_nonempty
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell
          (Recurrence.posDef_of_isRoundedGrid hq) r)
        (Recurrence.adaptedCell_nonempty (roundedGrid jStar (1 : Mat d)) r) hint)
  exact ⟨hsharp.trans hself, hupper⟩

end

end Initialization
end HighContrast
end Homogenization
