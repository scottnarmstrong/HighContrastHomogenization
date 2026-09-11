/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.IdentityMean
import HCPoly.Provider.Initialization.Transport

/-!
# Transport on the identity grid

The endpoint reference comparisons for standard cells give the identity
transport constant.  The fixed-grid mean order supplies its reverse order and
the nonnegative determinant increment.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Identity-grid means decrease with the scale. -/
theorem identity_mean_order [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {Q g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ}
    {jStar M r T : ℤ} (hw : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hjr : jStar ≤ r) (hrT : r ≤ T) (hTM : T ≤ M) :
    BlockMatLoewnerLE
        (adaptedMean P (roundedGrid jStar (1 : Mat d)) T)
        (adaptedMean P (roundedGrid jStar (1 : Mat d)) r) := by
  have hrM : r ≤ M := hrT.trans hTM
  have hjT : jStar ≤ T := hjr.trans hrT
  have hindexr := identity_admissible_index hw hjr hrM
  have hindexT := identity_admissible_index hw hjT hTM
  exact (mean_order_and_detIncrement_nonneg
    hP hw hY Matrix.PosDef.one hrT hindexr hindexT).1

/-- An earlier identity-grid mean is at most the intrinsic identity constant
times a later mean. -/
theorem identity_mean_le_later [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M r T : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hjr : jStar ≤ r) (hrT : r ≤ T) (hTM : T ≤ M) :
    BlockMatLoewnerLE
        (adaptedMean P (roundedGrid jStar (1 : Mat d)) r)
        (blockScale (initIdentityConst E)
          (adaptedMean P (roundedGrid jStar (1 : Mat d)) T)) := by
  have hrM : r ≤ M := hrT.trans hTM
  have hjT : jStar ≤ T := hjr.trans hrT
  have hmeanr := identity_mean_reference_comparison
    (P := P) (g := g) (E := E) (Ψ := Ψ) (K := K) (Cd := Cd)
    (jStar := jStar) (M := M) (r := r) hg hE hEpd hw hY hjr hrM
  have hmeanT := identity_mean_reference_comparison
    (P := P) (g := g) (E := E) (Ψ := Ψ) (K := K) (Cd := Cd)
    (jStar := jStar) (M := M) (r := T) hg hE hEpd hw hY hjT hTM
  have hupper0 := adaptedMean_le_reference_mul_four
    (P := P) (E := E) (B := 1)
    (q := roundedGrid jStar (1 : Mat d)) (r := r) (T := T)
    hE hEpd hsharp
    (by simpa only [one_mul] using hmeanr.2)
    (by simpa only [one_mul] using hmeanT.1)
    (show (1 : ℝ) ≤ 1 by norm_num)
  rw [initIdentityConst]
  convert hupper0 using 1
  ring_nf

/-- The identity-grid determinant increment is nonnegative and is bounded by
the logarithm of the intrinsic identity constant. -/
theorem identity_detIncrement_bounds [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M r T : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hjr : jStar ≤ r) (hrT : r ≤ T) (hTM : T ≤ M) :
    0 ≤ detIncrement P (roundedGrid jStar (1 : Mat d)) r T ∧
      detIncrement P (roundedGrid jStar (1 : Mat d)) r T ≤
        2 * (d : ℝ) * Real.log (initIdentityConst E) := by
  have hrM : r ≤ M := hrT.trans hTM
  have hjT : jStar ≤ T := hjr.trans hrT
  have hindexr := identity_admissible_index hw hjr hrM
  have hindexT := identity_admissible_index hw hjT hTM
  have hstruct := mean_order_and_detIncrement_nonneg
    hP hw hY Matrix.PosDef.one hrT hindexr hindexT
  have hupper := identity_mean_le_later
    (P := P) (g := g) (E := E) (Ψ := Ψ) (K := K) (Cd := Cd)
    (jStar := jStar) (M := M) (r := r) (T := T)
    hg hE hEpd hsharp hw hY hjr hrT hTM
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow
    hw Matrix.PosDef.one
  have hfinr := (finite_and_posDef_of_admissible
    hw hY Matrix.PosDef.one hindexr).1
  have hfinT := (finite_and_posDef_of_admissible
    hw hY Matrix.PosDef.one hindexT).1
  have hpdR := Recurrence.posDef_toFullBlockMat_adaptedMean hq r hfinr
  have hpdT := Recurrence.posDef_toFullBlockMat_adaptedMean hq T hfinT
  have hupperFull := le_of_blockMatLoewnerLE
    (Recurrence.isSymmetricBlockMat_adaptedMean
      P (roundedGrid jStar (1 : Mat d)) r)
    (isSymmetricBlockMat_blockScale _
      (Recurrence.isSymmetricBlockMat_adaptedMean
        P (roundedGrid jStar (1 : Mat d)) T)) hupper
  rw [toFullBlockMat_blockScale] at hupperFull
  have hC : 1 ≤ initIdentityConst E :=
    one_le_initIdentityConst hE hEpd hsharp
  have hdetUpper := log_det_sub_le_two_mul_log hpdR hpdT hC hupperFull
  rw [← Recurrence.detIncrement_eq_log_det_sub] at hdetUpper
  exact ⟨hstruct.2, hdetUpper⟩

end

end Initialization
end HighContrast
end Homogenization
