/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.Moments

/-!
# Initialization transport and determinant bounds

The endpoint mean comparisons and the intrinsic reference ratio compare any
earlier admissible mean with any later one by the printed initialization
constant.  Determinant monotonicity then gives the logarithmic increment bound.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

theorem log_det_sub_le_two_mul_log [Nonempty (Fin d)]
    {A B : FullBlockMat d} (hA : A.PosDef) (hB : B.PosDef)
    {c : ℝ} (hc : 1 ≤ c) (hle : A ≤ c • B) :
    Real.log A.det - Real.log B.det ≤ 2 * (d : ℝ) * Real.log c := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hdet := det_le_det_of_le hA (posDef_smul hB hcpos) hle
  rw [Matrix.det_smul, show Fintype.card (BlockCoord d) = 2 * d by
    simp [Fintype.card_sum, two_mul]] at hdet
  have hlog := Real.log_le_log hA.det_pos hdet
  rw [Real.log_mul (pow_ne_zero _ hcpos.ne') hB.det_pos.ne', Real.log_pow] at hlog
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlog
  linarith only [hlog]

/-- Endpoint comparisons against one reference block compare the two means by
`4 κ B²`. -/
theorem adaptedMean_le_reference_mul_four
    [Nonempty (Fin d)] {P : Measure (CoeffSpace d)}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {B : ℝ} {q : Mat d} {r T : ℤ}
    (hr : BlockMatLoewnerLE (adaptedMean P q r)
      (blockScale (B * 2) E))
    (hT : BlockMatLoewnerLE
      (blockScale (B * 2)⁻¹ (blockSharp E))
      (adaptedMean P q T)) (hB : 1 ≤ B) :
    BlockMatLoewnerLE (adaptedMean P q r)
      (blockScale (kappaRef E * B ^ 2 * 4) (adaptedMean P q T)) := by
  have hkap : 1 ≤ kappaRef E := one_le_kappaRef hE hEpd hsharp
  have hc : 0 < B * 2 :=
    mul_pos (lt_of_lt_of_le zero_lt_one hB) (by norm_num)
  have hmeanrSymm := Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hmeanTSymm := Recurrence.isSymmetricBlockMat_adaptedMean P q T
  have hrFull := le_of_blockMatLoewnerLE hmeanrSymm
    (isSymmetricBlockMat_blockScale _ hE) hr
  have href := blockMatLoewnerLE_reference_kappaRef_blockSharp hE hEpd
  have hrefFull := le_of_blockMatLoewnerLE hE
    (isSymmetricBlockMat_blockScale _
      (isSymmetricBlockMat_blockSharp hE hEpd)) href
  have hTFull := le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_blockScale _
      (isSymmetricBlockMat_blockSharp hE hEpd)) hmeanTSymm hT
  rw [toFullBlockMat_blockScale] at hrFull hrefFull hTFull
  have hsharpT : toFullBlockMat (blockSharp E) ≤
      (B * 2) • toFullBlockMat (adaptedMean P q T) := by
    have hscaled := smul_le_smul_of_le hc.le hTFull
    rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at hscaled
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  calc
    toFullBlockMat (adaptedMean P q r) ≤
        (B * 2) • toFullBlockMat E := hrFull
    _ ≤ (B * 2) •
        (kappaRef E • toFullBlockMat (blockSharp E)) :=
      smul_le_smul_of_le (by positivity) hrefFull
    _ = (B * 2 * kappaRef E) •
        toFullBlockMat (blockSharp E) := by rw [smul_smul]
    _ ≤ (B * 2 * kappaRef E) •
        ((B * 2) •
          toFullBlockMat (adaptedMean P q T)) :=
      smul_le_smul_of_le (by positivity) hsharpT
    _ = (kappaRef E * B ^ 2 * 4) • toFullBlockMat (adaptedMean P q T) := by
      rw [smul_smul]
      congr 1
      ring

/-- The exact mean transport and determinant-increment clause of the
initialization anchor. -/
theorem adaptedMean_transport_and_detIncrement [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} (hCd : 1 ≤ Cd) {jStar M : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu : Mat d} (hmu : mu.PosDef) {r T : ℤ} (hrT : r ≤ T)
    (hr : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r 0)
    (hT : IsAdmissibleIndex (roundedGrid jStar mu) jStar M T 0) :
    BlockMatLoewnerLE
        (adaptedMean P (roundedGrid jStar mu) T)
        (adaptedMean P (roundedGrid jStar mu) r) ∧
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid jStar mu) r)
        (blockScale (initGridConst Cd g E mu)
          (adaptedMean P (roundedGrid jStar mu) T)) ∧
      0 ≤ detIncrement P (roundedGrid jStar mu) r T ∧
      detIncrement P (roundedGrid jStar mu) r T ≤
        2 * (d : ℝ) * Real.log (initGridConst Cd g E mu) := by
  have hmeanr := adaptedMean_reference_comparison hg hE hEpd hCd hw hY hmu hr
  have hmeanT := adaptedMean_reference_comparison hg hE hEpd hCd hw hY hmu hT
  have hstruct := mean_order_and_detIncrement_nonneg hP hw hY hmu hrT hr hT
  have hupper0 := adaptedMean_le_reference_mul_four hE hEpd hsharp
    hmeanr.2 hmeanT.1 (one_le_boundaryConst hCd hg hmu)
  have hupper : BlockMatLoewnerLE
      (adaptedMean P (roundedGrid jStar mu) r)
      (blockScale (initGridConst Cd g E mu)
        (adaptedMean P (roundedGrid jStar mu) T)) := by
    simpa only [initGridConst] using hupper0
  have hq := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  have hfinr := Transport.hasFiniteAdaptedMean_of_isWindowMultiplier
    hY hmu hq hr.1 hr.2.2
  have hfinT := Transport.hasFiniteAdaptedMean_of_isWindowMultiplier
    hY hmu hq hT.1 hT.2.2
  have hpdR := Recurrence.posDef_toFullBlockMat_adaptedMean hq r hfinr
  have hpdT := Recurrence.posDef_toFullBlockMat_adaptedMean hq T hfinT
  have hupperFull := le_of_blockMatLoewnerLE
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu) r)
    (isSymmetricBlockMat_blockScale _
      (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu) T)) hupper
  rw [toFullBlockMat_blockScale] at hupperFull
  have hkap : 1 ≤ kappaRef E := one_le_kappaRef hE hEpd hsharp
  have hBsq : 1 ≤ boundaryConst Cd g mu ^ 2 := by
    have hB := one_le_boundaryConst hCd hg hmu
    nlinarith only [hB]
  have hC : 1 ≤ initGridConst Cd g E mu := by
    rw [initGridConst]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hkap hBsq) (by norm_num)
  have hdetUpper := log_det_sub_le_two_mul_log hpdR hpdT hC hupperFull
  rw [← Recurrence.detIncrement_eq_log_det_sub] at hdetUpper
  exact ⟨hstruct.1, hupper, hstruct.2, hdetUpper⟩

end

end Initialization
end HighContrast
end Homogenization
