/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.MeanComparison
import HCPoly.Provider.PortableHistory.CheckpointMoment
import HCPoly.Provider.Transport.CellDomination

/-!
# Raw and centered initialization moments

The averaged lower reference comparison turns the pathwise response bound into
a bound by the adapted mean itself.  The scalar-size and trace forms of the
Schatten estimates then put both the translated raw response and the centered
response below the same dimensional multiple of the common multiplier.
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

/-- A pathwise response bound and a lower mean comparison bound the response
in the mean normalization by the source initialization scale. -/
theorem toFullBlockMat_response_le_reference_mul
    [Nonempty (Fin d)]
    {A Em E : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hEm : IsSymmetricBlockMat Em) (hEmpd : Book.Ch02.BlockPosDef Em)
    {B y : ℝ} (hB : 1 ≤ B) (hy : 1 ≤ y)
    (hpath : BlockMatLoewnerLE A (blockScale (B * y) E))
    (hlow : BlockMatLoewnerLE (blockScale (B * 2)⁻¹ (blockSharp E)) Em) :
    toFullBlockMat A ≤ (kappaRef E * B ^ 2 * 4 * y) • toFullBlockMat Em := by
  have hkap : 1 ≤ kappaRef E := one_le_kappaRef hE hEpd hsharp
  have hBy : 0 ≤ B * y := mul_nonneg (le_trans zero_le_one hB) (le_trans zero_le_one hy)
  have hc : 0 < B * 2 := mul_pos (lt_of_lt_of_le zero_lt_one hB) (by norm_num)
  have href := blockMatLoewnerLE_reference_kappaRef_blockSharp hE hEpd
  have hpathFull := le_of_blockMatLoewnerLE hA
    (isSymmetricBlockMat_blockScale _ hE) hpath
  have hrefFull := le_of_blockMatLoewnerLE hE
    (isSymmetricBlockMat_blockScale _
      (isSymmetricBlockMat_blockSharp hE hEpd)) href
  rw [toFullBlockMat_blockScale] at hpathFull hrefFull
  have hlowFull := le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_blockScale _
      (isSymmetricBlockMat_blockSharp hE hEpd)) hEm hlow
  rw [toFullBlockMat_blockScale] at hlowFull
  have hsharpFull : toFullBlockMat (blockSharp E) ≤ (B * 2) • toFullBlockMat Em := by
    have hscaled := smul_le_smul_of_le hc.le hlowFull
    rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at hscaled
  have hcoef : B * y * kappaRef E * (B * 2) ≤ kappaRef E * B ^ 2 * 4 * y := by
    have hnonneg : 0 ≤ kappaRef E * B ^ 2 * y := by positivity
    calc
      B * y * kappaRef E * (B * 2) = 2 * (kappaRef E * B ^ 2 * y) := by ring
      _ ≤ 4 * (kappaRef E * B ^ 2 * y) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = kappaRef E * B ^ 2 * 4 * y := by ring
  calc
    toFullBlockMat A ≤ (B * y) • toFullBlockMat E := hpathFull
    _ ≤ (B * y) • (kappaRef E • toFullBlockMat (blockSharp E)) :=
      smul_le_smul_of_le hBy hrefFull
    _ = (B * y * kappaRef E) • toFullBlockMat (blockSharp E) := by rw [smul_smul]
    _ ≤ (B * y * kappaRef E) • ((B * 2) • toFullBlockMat Em) :=
      smul_le_smul_of_le (by positivity) hsharpFull
    _ = (B * y * kappaRef E * (B * 2)) • toFullBlockMat Em := by rw [smul_smul]
    _ ≤ (kappaRef E * B ^ 2 * 4 * y) • toFullBlockMat Em :=
      smul_le_smul_of_scalar_le
        (posDef_toFullBlockMat hEm hEmpd).posSemidef hcoef

/-- A positive response below `c` times its mean has both raw and centered
Schatten size below the same explicit dimensional multiple of `c`. -/
theorem raw_and_centered_schattenSize_le [NeZero d]
    {A Em : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hApsd : (toFullBlockMat A).PosSemidef) (hEm : IsSymmetricBlockMat Em)
    (hEmpd : Book.Ch02.BlockPosDef Em) {Q c : ℝ} (hQ : 0 < Q) (hc : 1 ≤ c)
    (hle : toFullBlockMat A ≤ c • toFullBlockMat Em) :
    schattenSize Q A Em ≤ (2 * d : ℝ) ^ Q⁻¹ * ((1 + 2 * (d : ℝ)) * c) ∧
      schattenSize Q (blockSub A Em) Em ≤
        (2 * d : ℝ) ^ Q⁻¹ * ((1 + 2 * (d : ℝ)) * c) := by
  have hEmpdFull := posDef_toFullBlockMat hEm hEmpd
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hdim0 : 0 ≤ (2 * d : ℝ) := by positivity
  have hfac0 : 0 ≤ (2 * d : ℝ) ^ Q⁻¹ := Real.rpow_nonneg hdim0 _
  have hsize : blockSize A Em ≤ c := by
    rw [blockSize_eq_relSize hA hEm hEmpd hApsd]
    exact (relSize_le_iff hApsd hEmpdFull hc0).mpr hle
  have hraw := PortableHistory.schattenSize_le_blockSize hA hEm hEmpd hQ
  have htrace := Transport.trace_toFullBlockMat_normalizedBlock_le hEmpdFull hle
  have htraceSelf : Matrix.trace (toFullBlockMat (normalizedBlock Em Em)) =
      2 * (d : ℝ) := by
    rw [Recurrence.toFullBlockMat_normalizedBlock, matSqrt_inv_conj hEmpdFull,
      Matrix.trace_one]
    simp [Fintype.card_sum, two_mul]
  rw [htraceSelf] at htrace
  have hcenter := Transport.schattenSize_blockSub_le_of_trace_le hQ hA hApsd hEm
    hEmpdFull htrace
  have htrace0 : 0 ≤ c * (2 * (d : ℝ)) := mul_nonneg hc0 hdim0
  rw [abs_of_nonneg htrace0] at hcenter
  have hwidth : 1 + c * (2 * (d : ℝ)) ≤ (1 + 2 * (d : ℝ)) * c := by
    have hstep : 1 + c * (2 * (d : ℝ)) ≤ c + c * (2 * (d : ℝ)) := by
      linarith only [hc]
    exact hstep.trans_eq (by ring)
  have hcwide : c ≤ (1 + 2 * (d : ℝ)) * c := by
    have hone : (1 : ℝ) ≤ 1 + 2 * (d : ℝ) := by linarith only [hdim0]
    calc
      c = 1 * c := (one_mul c).symm
      _ ≤ (1 + 2 * (d : ℝ)) * c := mul_le_mul_of_nonneg_right hone hc0
  constructor
  · exact hraw.trans <| (mul_le_mul_of_nonneg_left hsize hfac0).trans <|
      mul_le_mul_of_nonneg_left hcwide hfac0
  · exact hcenter.trans (mul_le_mul_of_nonneg_left hwidth hfac0)

/-- The raw translated response and the centered response satisfy the exact
initialization moment bounds with an explicit admissible dimensional constant. -/
theorem adapted_moment_bounds [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} (hCd : 1 ≤ Cd) {jStar M : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu : Mat d} (hmu : mu.PosDef) {r : ℤ} {w : Fin d → ℤ}
    (hindex : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r w) :
    lqSchattenSize P ((initExpQ d g : ℕ) : ℝ)
        (adaptedResponse (roundedGrid jStar mu) r w)
        (adaptedMean P (roundedGrid jStar mu) r) ≤
      ENNReal.ofReal
        ((2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
            (1 + 2 * (d : ℝ))) * initGridConst Cd g E mu) ∧
      centeredMoment P ((initExpQ d g : ℕ) : ℝ)
          (roundedGrid jStar mu) r ≤
        ENNReal.ofReal
          ((2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
              (1 + 2 * (d : ℝ))) * initGridConst Cd g E mu) := by
  set q : Mat d := roundedGrid jStar mu with hq
  set Em : BlockMat d := adaptedMean P q r with hEm
  set Q : ℝ := ((initExpQ d g : ℕ) : ℝ) with hQdef
  set C : ℝ := initGridConst Cd g E mu with hCdef
  set L : ℝ := (2 * d : ℝ) ^ Q⁻¹ * (1 + 2 * (d : ℝ)) with hLdef
  have hQ2 : (2 : ℝ) ≤ Q := by rw [hQdef]; exact two_le_initExpQ hg
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num) hQ2
  have hqgrid := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  rw [← hq] at hqgrid
  have hzero : adaptedCellAt q r 0 = adaptedCell q r := PortableHistory.adaptedCellAt_zero q r
  have hindex0 : IsAdmissibleIndex q jStar M r 0 :=
    ⟨hindex.1, by rw [hzero]; exact hindex.2.2, hindex.2.2⟩
  have hindex0' : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r 0 := by
    simpa only [hq] using hindex0
  have hmean := adaptedMean_reference_comparison hg hE hEpd hCd hw hY hmu
    hindex0'
  rw [← hq, ← hEm] at hmean
  have hEmSymm : IsSymmetricBlockMat Em := by
    rw [hEm]
    exact Recurrence.isSymmetricBlockMat_adaptedMean P q r
  have hEmPd : Book.Ch02.BlockPosDef Em := by
    rw [hEm]
    exact Transport.blockPosDef_adaptedMean_of_isWindowMultiplier
      hY hmu hqgrid hindex.1 hindex.2.2
  have hB1 : 1 ≤ boundaryConst Cd g mu := one_le_boundaryConst hCd hg hmu
  have hkap1 : 1 ≤ kappaRef E := one_le_kappaRef hE hEpd hsharp
  have hBsq : 1 ≤ boundaryConst Cd g mu ^ 2 := by
    nlinarith only [hB1]
  have hC1 : 1 ≤ C := by
    rw [hCdef, initGridConst]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hkap1 hBsq) (by norm_num)
  have hpath := ae_adaptedResponse_and_coarseStarInv_le hY
  have hpt : ∀ᵐ a ∂P,
      schattenSize Q (adaptedResponse q r w a) Em ≤ L * C * Y a ∧
        schattenSize Q
          (blockSub (coarseBlock (adaptedCell q r) a) Em) Em ≤ L * C * Y a := by
    filter_upwards [hpath] with a ha
    have haw := (ha mu hmu r w hindex).1
    have ha0 := (ha mu hmu r 0 hindex0).1
    rw [← hq] at haw ha0
    have hAwSymm : IsSymmetricBlockMat (adaptedResponse q r w a) := by
      exact isSymmetricBlockMat_coarseBlock _ a
    have hA0Symm : IsSymmetricBlockMat (coarseBlock (adaptedCell q r) a) :=
      isSymmetricBlockMat_coarseBlock _ a
    have hAwPsd : (toFullBlockMat (adaptedResponse q r w a)).PosSemidef :=
      (posDef_toFullBlockMat hAwSymm
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt
          (Recurrence.posDef_of_isRoundedGrid hqgrid) r w a)).posSemidef
    have hA0Psd : (toFullBlockMat (coarseBlock (adaptedCell q r) a)).PosSemidef :=
      (posDef_toFullBlockMat hA0Symm
        (Recurrence.blockPosDef_coarseBlock_adaptedCell
          (Recurrence.posDef_of_isRoundedGrid hqgrid) r a)).posSemidef
    have hdomw := toFullBlockMat_response_le_reference_mul
      hAwSymm hE hEpd hsharp hEmSymm hEmPd
      hB1 (hY.one_le a) haw hmean.1
    have hdom0 := toFullBlockMat_response_le_reference_mul
      hA0Symm hE hEpd hsharp hEmSymm hEmPd
      hB1 (hY.one_le a) (by simpa only [adaptedResponse, hzero] using ha0) hmean.1
    have hdomwC : toFullBlockMat (adaptedResponse q r w a) ≤
        (C * Y a) • toFullBlockMat Em := by
      simpa only [hCdef, initGridConst] using hdomw
    have hdom0C : toFullBlockMat (coarseBlock (adaptedCell q r) a) ≤
        (C * Y a) • toFullBlockMat Em := by
      simpa only [hCdef, initGridConst] using hdom0
    have hcY : 1 ≤ C * Y a := one_le_mul_of_one_le_of_one_le hC1 (hY.one_le a)
    have hwsize := raw_and_centered_schattenSize_le hAwSymm hAwPsd hEmSymm
      hEmPd hQ0 hcY hdomwC
    have h0size := raw_and_centered_schattenSize_le hA0Symm hA0Psd hEmSymm
      hEmPd hQ0 hcY hdom0C
    rw [hLdef]
    exact ⟨by simpa only [mul_assoc] using hwsize.1,
      by simpa only [mul_assoc] using h0size.2⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hLC0 : 0 ≤ L * C := mul_nonneg hL0 hC0
  have hraw : lqSchattenSize P Q (adaptedResponse q r w) Em ≤
      eLpNorm ((L * C) • Y) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hpt] with a ha
    have hleft : 0 ≤ schattenSize Q (adaptedResponse q r w a) Em :=
      Recurrence.zero_le_schattenNorm
        (isSymmetricBlockMat_normalizedBlock (isSymmetricBlockMat_coarseBlock _ a)) Q
    change ‖schattenSize Q (adaptedResponse q r w a) Em‖ ≤ ‖(L * C) * Y a‖
    rw [Real.norm_of_nonneg hleft,
      Real.norm_of_nonneg (mul_nonneg hLC0 (le_trans zero_le_one (hY.one_le a)))]
    exact ha.1
  have hcenter : centeredMoment P Q q r ≤
      eLpNorm ((L * C) • Y) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hpt] with a ha
    have hleft : 0 ≤ schattenSize Q
        (blockSub (coarseBlock (adaptedCell q r) a) Em) Em :=
      Recurrence.zero_le_schattenNorm
        (isSymmetricBlockMat_normalizedBlock
          (isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ a) hEmSymm)) Q
    change ‖schattenSize Q
      (blockSub (coarseBlock (adaptedCell q r) a) Em) Em‖ ≤ ‖(L * C) * Y a‖
    rw [Real.norm_of_nonneg hleft,
      Real.norm_of_nonneg (mul_nonneg hLC0 (le_trans zero_le_one (hY.one_le a)))]
    exact ha.2
  have hYnorm : lqNorm P Q Y ≤ 2 := by
    rw [hQdef]
    exact (initialization_multiplier_bounds hg hw hY).2
  have hcommon : eLpNorm ((L * C) • Y) (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal ((2 * L) * C) := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hLC0]
    calc
      ENNReal.ofReal (L * C) * lqNorm P Q Y ≤ ENNReal.ofReal (L * C) * 2 :=
        by gcongr
      _ = ENNReal.ofReal ((2 * L) * C) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_mul hLC0]
        congr 1
        ring
  have hraw' := hraw.trans hcommon
  have hcenter' := hcenter.trans hcommon
  simpa only [hQdef, hq, hEm, hLdef, hCdef, mul_assoc] using And.intro hraw' hcenter'

end

end Initialization
end HighContrast
end Homogenization
