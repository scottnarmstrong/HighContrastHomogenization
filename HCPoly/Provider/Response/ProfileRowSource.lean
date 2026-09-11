/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowAligned
import HCPoly.Provider.SourceControl.ResponseRowSeries
import HCPoly.Provider.Transport.TransportCoefficients
import HCPoly.Provider.Transport.WindowTerminalNormalization

/-!
# The response row below the alignment scale

The source row is converted from the reference block to the adapted terminal
mean using the reference contrast and the lower endpoint comparison.  The
coefficient-transpose row is the sign-congruence image of the primal row, not
the sharp row retained separately by source control.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem source_reference_quadratic_le [NeZero d]
    {P : Measure (CoeffSpace d)} {g Cd : ℝ} {E : BlockMat d}
    {jStar : ℤ} {m0 : Mat d} {s t : ℤ} {Y : CoeffSpace d → ℝ}
    (hCd : 0 < Cd) (hg : g < 1) (hm0 : m0.PosDef)
    (hfields : IsWindowedSourceFields P g Cd E jStar m0 s t Y)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul E X) ≤
      kappaRef E * boundaryConst Cd g m0 * 2 *
        blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X) := by
  let B : ℝ := boundaryConst Cd g m0
  have hB : 0 < B := Transport.zero_lt_boundaryConst hCd hg hm0
  have hB2 : 0 < B * 2 := mul_pos hB (by norm_num)
  have href := hfields.refContrast_le X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at href
  have href' :
      blockVecDot X (blockMatVecMul E X) ≤
        kappaRef E * blockVecDot X (blockMatVecMul (blockSharp E) X) := by
    linarith only [href]
  have hlow := (hfields.reference s (Or.inl rfl)).1 X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hlow
  have hlow' :
      (B * 2)⁻¹ * blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
        blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X) := by
    simpa only [B] using (show
      (boundaryConst Cd g m0 * 2)⁻¹ *
          blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
        blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X) by
      linarith only [hlow])
  have hsharp :
      blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
        (B * 2) * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X) := by
    calc
      blockVecDot X (blockMatVecMul (blockSharp E) X) =
          (B * 2) * ((B * 2)⁻¹ *
            blockVecDot X (blockMatVecMul (blockSharp E) X)) := by
        field_simp [hB2.ne']
      _ ≤ (B * 2) * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X) :=
        mul_le_mul_of_nonneg_left hlow' hB2.le
  calc
    blockVecDot X (blockMatVecMul E X) ≤
        kappaRef E * blockVecDot X (blockMatVecMul (blockSharp E) X) := href'
    _ ≤ kappaRef E * ((B * 2) *
        blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X)) :=
      mul_le_mul_of_nonneg_left hsharp (Transport.zero_le_kappaRef E)
    _ = _ := by ring

/-- The primal source row below the alignment scale, converted to the terminal
adapted mean with the cap-two coefficient. -/
theorem profilePrimalSourceQuadraticRow_le [NeZero d]
    {P : Measure (CoeffSpace d)} {g Cd : ℝ} {E : BlockMat d}
    {jStar : ℤ} {m0 : Mat d} {s t : ℤ} {Y : CoeffSpace d → ℝ}
    (hCd : 0 < Cd) (hg : g < 1) (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0)) (hjs : jStar ≤ s)
    (hfields : IsWindowedSourceFields P g Cd E jStar m0 s t Y)
    {Klo : ℤ} (hKlo : Klo < jStar) (X : BlockVec d) :
    ∑ k ∈ Finset.Ico Klo jStar, profileRowWeight k s *
        avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          blockVecDot X
            (blockMatVecMul
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w)) X)) ≤
      kappaRef E * boundaryConst Cd g m0 ^ 2 * 2 ^ 2 /
          ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) *
        blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X) := by
  let q0 : Mat d := roundedGrid jStar m0
  let B : ℝ := boundaryConst Cd g m0
  have hCtr : ∀ k : ℤ, k < jStar → ∀ w : Fin d → ℤ,
      w ∈ alignedIndex q0 k s ↔
        adaptedCellCenter q0 k w ∈ adaptedCell q0 s := by
    intro k hk w
    exact mem_alignedIndex_iff (Recurrence.posDef_of_isRoundedGrid hgrid)
      (le_trans hk.le hjs)
  have hrow := (hfields.rows (fun k ↦ alignedIndex q0 k s) hCtr
    Klo hKlo X).1
  have hbase := source_reference_quadratic_le hCd hg hm0 hfields X
  have hB : 0 < B := Transport.zero_lt_boundaryConst hCd hg hm0
  have hpow : (1 : ℝ) < (3 : ℝ) ^ (3 / 2 - g) :=
    SourceControl.one_lt_rpow_sub (show g < (3 / 2 : ℝ) by linarith only [hg])
  have hden : 0 < (3 : ℝ) ^ (3 / 2 - g) - 1 := by
    linarith only [hpow]
  have hdecay : 0 ≤
      (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hcoef : 0 ≤
      B * 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) :=
    mul_nonneg (div_nonneg (mul_nonneg hB.le (by norm_num)) hden.le) hdecay
  calc
    ∑ k ∈ Finset.Ico Klo jStar, profileRowWeight k s *
        avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          blockVecDot X
            (blockMatVecMul
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w)) X)) ≤
      B * 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) *
        blockVecDot X (blockMatVecMul E X) := by
      simpa only [profileRowWeight, avsum_eq, q0, B] using hrow
    _ ≤ (B * 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ)))) *
        (kappaRef E * B * 2 *
          blockVecDot X
            (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X)) :=
      mul_le_mul_of_nonneg_left hbase hcoef
    _ = _ := by ring

end

end Homogenization.HighContrast.Response
