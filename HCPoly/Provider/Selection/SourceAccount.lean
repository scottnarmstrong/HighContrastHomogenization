/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.SourceControl.SourceControlAssembly
import HCPoly.Provider.Initialization.ReferenceComparison
import HCPoly.Provider.Initialization.Reference
import HCPoly.Provider.Initialization.Structural
import HCPoly.Provider.ShortHop.PathStep
import HCPoly.Setup.SelectionObjects

/-!
# Source data attached to the selected terminal tuple

The terminal enclosure places every adapted cell read by the source account
inside the execution window.  The window multiplier and source-control
estimates then supply the cellwise fields, response rows, reference comparison,
and the below-start maximum required by the global selector.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem lt_initExpRhoMax (d : ℕ) {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    g < initExpRhoMax d g := by
  have hQ : (2 : ℝ) ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast Initialization.two_le_initExpQ (d := d) (g := g) hg
  have ha : 0 < initExpA g := by
    have := hg.2
    simp only [initExpA]
    linarith only [this]
  have hnum : 0 < (d : ℝ) + initExpA g := by positivity
  have : 0 < ((d : ℝ) + initExpA g) / (initExpQ d g : ℝ) := by
    apply div_pos hnum
    linarith only [hQ]
  simp only [initExpRhoMax]
  linarith only [this]

private theorem integral_le_two {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) :
    (∫ a, Y a ∂P) ≤ 2 := by
  have hQ1 : (1 : ℝ) ≤ (initExpQ d g : ℝ) := by
    have := Initialization.two_le_initExpQ (d := d) (g := g) hg
    linarith only [this]
  have h1 := Transport.ofReal_integral_le_lqNorm hY hQ1
  have h2 := Transport.lqNorm_le_two (Q := (initExpQ d g : ℝ)) hQ1 hwin hY
  have h3 : ENNReal.ofReal (∫ a, Y a ∂P) ≤ ENNReal.ofReal 2 := by
    have : (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) := by simp
    rw [this]
    exact le_trans h1 h2
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h3

private theorem quad_nonneg {A : BlockMat d}
    (hA : Book.Ch02.BlockPosDef A) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  rcases eq_or_ne X 0 with h | h
  · subst h
    simp [blockMatVecMul, blockVecDot, vecDot, matVecMul]
  · exact (hA X h).le

private theorem blockScale_mono {A : BlockMat d}
    (hA : Book.Ch02.BlockPosDef A) {c c' : ℝ} (h : c ≤ c') :
    BlockMatLoewnerLE (blockScale c A) (blockScale c' A) := by
  intro X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale,
    Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hq := quad_nonneg hA X
  nlinarith only [hq, h]

/-- The whole source account of the selected terminal tuple follows from its
execution-window enclosure. -/
theorem selection_source_account {d : ℕ} {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] [NeZero d]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {Cd : ℝ} (hCd : 1 ≤ Cd) {jdag Mexec : ℤ}
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jdag Mexec)
    {E0 : BlockMat d} (hE0s : IsSymmetricBlockMat E0)
    (hE0p : Book.Ch02.BlockPosDef E0)
    {m0 q : Mat d} {s t : ℤ}
    (hm0 : m0 = canonicalMetric E0) (hq : q = roundedGrid jdag m0)
    (hs : jdag ≤ s) (hst : s < t)
    (henc1 : ∀ k : ℤ, jdag ≤ k → k ≤ t →
      adaptedCell q k ⊆ centeredCube d Mexec)
    (henc2 : ∀ k : ℤ, k < jdag → ∀ v : ℤ, v = s ∨ v = t →
      ∀ z ∈ containedCenters q k v,
        adaptedCellTranslate q k z ⊆ centeredCube d Mexec)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jdag Mexec Y) :
    IsWindowedSourceFields P g Cd E jdag m0 s t Y ∧
      eLpNorm
          (belowStartSup (initExpRhoMax d g) q jdag t
            (fun k => containedCenters q k t) (adaptedMean P q t))
          (ENNReal.ofReal (initExpQ d g : ℝ)) P ≤
        ENNReal.ofReal
          (initGridConst Cd g E m0 *
            (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ)))) := by
  subst hq
  have hE : IsSymmetricBlockMat E := hdag.refBlock_isSymm
  have hEpd : Book.Ch02.BlockPosDef E := hdag.refBlock_posDef
  have hg1 : g < 1 := hg.2
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hm0pd : m0.PosDef := by
    subst hm0
    exact ShortHop.posDef_canonicalMetric (posDef_toFullBlockMat hE0s hE0p)
  have hqr : IsRoundedGrid jdag (roundedGrid jdag m0) :=
    Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hwin hm0pd
  have hint2 : (∫ a, Y a ∂P) ≤ 2 := integral_le_two hg hwin hY
  have hint1 : (1 : ℝ) ≤ ∫ a, Y a ∂P :=
    Transport.one_le_integral_of_isWindowMultiplier hY
  have hbpos : 0 < boundaryConst Cd g m0 :=
    Transport.zero_lt_boundaryConst hCd0 hg1 hm0pd
  have hrho : g < initExpRhoMax d g := lt_initExpRhoMax d hg
  have hQ1 : (1 : ℝ) ≤ (initExpQ d g : ℝ) := by
    have := Initialization.two_le_initExpQ (d := d) (g := g) hg
    linarith only [this]
  have hjt : jdag ≤ t := le_trans hs hst.le
  have hcellS : adaptedCell (roundedGrid jdag m0) s ⊆ centeredCube d Mexec :=
    henc1 s hs hst.le
  have hcellT : adaptedCell (roundedGrid jdag m0) t ⊆ centeredCube d Mexec :=
    henc1 t hjt le_rfl
  have hsharpsym : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_blockSharp hE hEpd
  have hsharppd : Book.Ch02.BlockPosDef (blockSharp E) := by
    refine (blockPosDef_iff_posDef hsharpsym).mpr ?_
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp (posDef_toFullBlockMat hE hEpd)
  have hscal : boundaryConst Cd g m0 * (∫ a, Y a ∂P) ≤
      boundaryConst Cd g m0 * 2 :=
    mul_le_mul_of_nonneg_left hint2 hbpos.le
  have hscalpos : 0 < boundaryConst Cd g m0 * (∫ a, Y a ∂P) :=
    mul_pos hbpos (lt_of_lt_of_le zero_lt_one hint1)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · filter_upwards [hY.adapted_primal, hY.adapted_adjoint] with a hap haa
    intro k hk v hv z hz
    exact ⟨hap m0 hm0pd k z (henc2 k hk v hv z hz),
      haa m0 hm0pd k z (henc2 k hk v hv z hz)⟩
  · intro Ctr hCtr Klo hKlo X
    have hlam : g < (3 : ℝ) / 2 := by linarith only [hg1]
    have hrow := SourceControl.response_row_of_isWindowMultiplier hCd0.le hg1 hE hEpd hY
      hm0pd hqr t s hs hst hcellS ((3 : ℝ) / 2) hlam Ctr hCtr Klo hKlo X
    have hD : (0 : ℝ) < (3 : ℝ) ^ ((3 : ℝ) / 2 - g) - 1 := by
      have := SourceControl.one_lt_rpow_sub hlam
      linarith only [this]
    have hw : (0 : ℝ) <
        (3 : ℝ) ^ (-((3 : ℝ) / 2) * ((s : ℝ) - (jdag : ℝ))) := by
      positivity
    have hc : boundaryConst Cd g m0 * (∫ a, Y a ∂P) /
          ((3 : ℝ) ^ ((3 : ℝ) / 2 - g) - 1) ≤
        boundaryConst Cd g m0 * 2 /
          ((3 : ℝ) ^ ((3 : ℝ) / 2 - g) - 1) := by
      gcongr
    refine ⟨le_trans hrow.1 ?_, le_trans hrow.2 ?_⟩
    · have hqf := quad_nonneg hEpd X
      have hbound :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hw.le) hqf
      linarith only [hbound]
    · have hqf := quad_nonneg (Transport.blockPosDef_blockReflect hEpd) X
      have hbound :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hw.le) hqf
      linarith only [hbound]
  · intro v hv
    have hcell : adaptedCell (roundedGrid jdag m0) v ⊆ centeredCube d Mexec := by
      rcases hv with rfl | rfl
      · exact hcellS
      · exact hcellT
    have hjv : jdag ≤ v := by
      rcases hv with rfl | rfl
      · exact hs
      · exact hjt
    have hlow := Transport.blockScale_inv_blockSharp_le_adaptedMean hCd0 hg1 hE hEpd
      hY hm0pd hqr hjv hcell
    have hup := Transport.adaptedMean_le_blockScale hE hY hm0pd hqr hjv hcell
    have hinv : (boundaryConst Cd g m0 * 2)⁻¹ ≤
        (boundaryConst Cd g m0 * (∫ a, Y a ∂P))⁻¹ := by
      gcongr
    have hlow2 : BlockMatLoewnerLE
        (blockScale (boundaryConst Cd g m0 * 2)⁻¹ (blockSharp E))
        (adaptedMean P (roundedGrid jdag m0) v) :=
      BlockMatLoewnerLE.trans (blockScale_mono hsharppd hinv) hlow
    have hup2 : BlockMatLoewnerLE
        (adaptedMean P (roundedGrid jdag m0) v)
        (blockScale (boundaryConst Cd g m0 * 2) E) :=
      BlockMatLoewnerLE.trans hup (blockScale_mono hEpd hscal)
    refine ⟨hlow2, hup2, ?_, ?_⟩
    · rw [Transport.blockScale_blockReflect]
      exact Transport.blockMatLoewnerLE_blockReflect hlow2
    · rw [Transport.blockScale_blockReflect]
      exact Transport.blockMatLoewnerLE_blockReflect hup2
  · exact Initialization.blockMatLoewnerLE_reference_kappaRef_blockSharp hE hEpd
  · exact Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
  · have hFsym : IsSymmetricBlockMat
        (adaptedMean P (roundedGrid jdag m0) t) :=
      Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jdag m0) t
    have hFpd : Book.Ch02.BlockPosDef
        (adaptedMean P (roundedGrid jdag m0) t) :=
      Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hm0pd hqr hjt hcellT
    have hZ : ∀ k < jdag,
        ∀ z ∈ (fun k => containedCenters (roundedGrid jdag m0) k t) k,
          adaptedCellTranslate (roundedGrid jdag m0) k z ⊆ centeredCube d Mexec :=
      fun k hk z hz => henc2 k hk t (Or.inr rfl) z hz
    have hmain := Transport.eLpNorm_belowStartSup_le hCd0.le hg1 hE hEpd hY hm0pd
      hqr hFsym hFpd hrho t hZ (initExpQ d g : ℝ)
    have hsize := Transport.blockSize_adaptedMean_le hCd0 hg1 hE hEpd hY hm0pd hqr
      hjt hcellT
    have hlq := Transport.lqNorm_le_two (Q := (initExpQ d g : ℝ)) hQ1 hwin hY
    have hkap : (1 : ℝ) ≤ kappaRef E :=
      Initialization.one_le_kappaRef hE hEpd
        (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
    have hpow : (0 : ℝ) <
        (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ))) := by
      positivity
    have hsize2 : blockSize E (adaptedMean P (roundedGrid jdag m0) t) ≤
        kappaRef E * (boundaryConst Cd g m0 * 2) := by
      refine le_trans hsize ?_
      have : (0 : ℝ) ≤ kappaRef E := by linarith only [hkap]
      exact mul_le_mul_of_nonneg_left hscal this
    have hreal : boundaryConst Cd g m0 *
          blockSize E (adaptedMean P (roundedGrid jdag m0) t) *
          (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ))) * 2 ≤
        initGridConst Cd g E m0 *
          (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ))) := by
      have h1 : boundaryConst Cd g m0 *
          blockSize E (adaptedMean P (roundedGrid jdag m0) t) ≤
          boundaryConst Cd g m0 *
            (kappaRef E * (boundaryConst Cd g m0 * 2)) :=
        mul_le_mul_of_nonneg_left hsize2 hbpos.le
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h1 hpow.le) (by norm_num : (0 : ℝ) ≤ 2)
      refine le_trans h2 (le_of_eq ?_)
      simp only [initGridConst]
      ring
    have hnn : (0 : ℝ) ≤ boundaryConst Cd g m0 *
        blockSize E (adaptedMean P (roundedGrid jdag m0) t) *
        (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ))) := by
      have hbs : (0 : ℝ) ≤ blockSize E
          (adaptedMean P (roundedGrid jdag m0) t) :=
        PortableHistory.blockSize_nonneg hE hFsym hFpd
      positivity
    calc
      eLpNorm
            (belowStartSup (initExpRhoMax d g) (roundedGrid jdag m0) jdag t
              (fun k => containedCenters (roundedGrid jdag m0) k t)
              (adaptedMean P (roundedGrid jdag m0) t))
            (ENNReal.ofReal (initExpQ d g : ℝ)) P
          ≤ ENNReal.ofReal (boundaryConst Cd g m0 *
                blockSize E (adaptedMean P (roundedGrid jdag m0) t) *
                (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ)))) *
              lqNorm P (initExpQ d g : ℝ) Y := hmain
      _ ≤ ENNReal.ofReal (boundaryConst Cd g m0 *
                blockSize E (adaptedMean P (roundedGrid jdag m0) t) *
                (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ)))) *
              ENNReal.ofReal 2 := by
            gcongr
            · simpa using hlq
      _ = ENNReal.ofReal (boundaryConst Cd g m0 *
                blockSize E (adaptedMean P (roundedGrid jdag m0) t) *
                (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ))) *
              2) := by
            rw [← ENNReal.ofReal_mul hnn]
      _ ≤ ENNReal.ofReal (initGridConst Cd g E m0 *
              (3 : ℝ) ^ (-initExpRhoMax d g * ((t : ℝ) - (jdag : ℝ)))) :=
            ENNReal.ofReal_le_ofReal hreal

end

end Homogenization.HighContrast.Selection
