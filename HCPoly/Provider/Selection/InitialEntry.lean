/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.InitialCheckpoint
import HCPoly.Provider.Selection.BranchFixed
import HCPoly.Provider.Selection.Potential
import HCPoly.Provider.Selection.Termination
import HCPoly.Provider.Selection.DeterminantPrefix
import HCPoly.Provider.Initialization.IdentityClause
import HCPoly.Provider.Initialization.Reference
import HCPoly.Provider.SourceControl.SchurHelpers

/-!
# The initialized selector entry

The identity-grid hitting argument supplies one bounded checkpoint.  The
identity comparison and portable-history laws then package that checkpoint as
the exact fresh state from which the selector is run.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The identity-grid provider produces the exact fresh entry state together
with every quantitative bound used by the capped-run argument. -/
theorem exists_initialSelectionEntry (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
      (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g))
    {Chit Bmin : ℝ} (initData : InitialProviderData c c.etaInit Chit)
    (cc : CutoffConstants c w.alphaFresh w.alphaX
      (2 * (d : ℝ) * Real.log 12) w.c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {source : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K source)
    {Lam : ℝ} (hLamEq : Lam = Real.logb 3 (2 + aspectRatio E))
    {jdag Mexec : ℤ}
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jdag Mexec)
    (hMexec : Mexec = jdag + ⌈cc.Cexec * Lam⌉)
    {Yaux : CoeffSpace d → ℝ}
    (hYaux : IsWindowMultiplier P g E Psi K Cd jdag Mexec Yaux) :
    ∃ (r0 : ℤ) (A0 : BlockMat d) (hcen hnl : ℝ≥0∞),
      jdag + ⌈cc.B * Lam⌉ ≤ r0 ∧
        (r0 : ℝ) ≤ (jdag : ℝ) + cc.CR * Lam ∧ r0 ≤ Mexec ∧
        IsSymmetricBlockMat A0 ∧ Book.Ch02.BlockPosDef A0 ∧
        ExactStateData P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jdag (initialState r0 A0 hcen hnl) ∧
        FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jdag
          (initialState r0 A0 hcen hnl) ∧
        stateProfile P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) jdag (initialState r0 A0 hcen hnl) ≤
          ENNReal.ofReal c.etaReady ∧
        stateProjectiveDistance (initialState r0 A0 hcen hnl) ≤
          (2 * (d : ℝ) * Real.log 12) * Lam ∧
        adaptedDetRoot P (1 : Mat d) r0 ≤ 24 * aspectRatio E ∧
        statePotential P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) (initExpRhoDr g) jdag c.etaReady c.etaPre
            w.alphaW w.alphaX w.alphaFresh w.alphaSearch
            (initialState r0 A0 hcen hnl) ≤ cc.CF * Lam := by
  let : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hPi : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hLam : 1 ≤ Lam := by
    rw [hLamEq]
    exact ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hLam0 : 0 ≤ Lam := le_trans zero_le_one hLam
  have hceilB0 : (0 : ℤ) ≤ ⌈cc.B * Lam⌉ :=
    Int.ceil_nonneg (mul_nonneg cc.B_pos.le hLam0)
  let R : ℤ := jdag + ⌈cc.B * Lam⌉
  have hjR : jdag ≤ R := by dsimp [R]; omega
  have hCRCM : cc.CR ≤ cc.CM := by
    rw [cc.CM_eq, executionMinimum_eq]
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hspan : 0 ≤ cc.Lexec + c.chop / Real.log 3 :=
      add_nonneg cc.Lexec_pos.le (div_nonneg c.chop_pos.le hlog3.le)
    have hcount : 0 ≤ cc.CN + 3 := by linarith only [cc.CN_pos]
    have hceil : 0 ≤ (⌈(1 / 2 : ℝ) * Real.logb 3 d⌉₊ : ℝ) := by positivity
    have hextra : 0 ≤ (cc.Lexec + c.chop / Real.log 3) * (cc.CN + 3) :=
      mul_nonneg hspan hcount
    linarith only [hextra, hceil]
  have hCRCexec : cc.CR ≤ cc.Cexec := hCRCM.trans cc.CM_le_Cexec
  have hcoeff : cc.B + Chit + 1 ≤ cc.Cexec := by
    simpa only [cc.CR_eq, checkpointCoefficient_eq] using hCRCexec
  have hcoeffLam :
      cc.B * Lam + Chit * Lam + 1 ≤ cc.Cexec * Lam := by
    have hmul := mul_le_mul_of_nonneg_right hcoeff hLam0
    have hLamOne : 1 ≤ Lam := hLam
    calc
      cc.B * Lam + Chit * Lam + 1 ≤
          cc.B * Lam + Chit * Lam + Lam := by linarith only [hLamOne]
      _ = (cc.B + Chit + 1) * Lam := by ring
      _ ≤ cc.Cexec * Lam := hmul
  have hroom : R + ⌈Chit * Lam⌉ ≤ Mexec := by
    have hceilSum : ⌈cc.B * Lam⌉ + ⌈Chit * Lam⌉ ≤ ⌈cc.Cexec * Lam⌉ := by
      calc
        _ ≤ ⌈cc.B * Lam + Chit * Lam⌉ + 1 :=
          Int.ceil_add_ceil_le _ _
        _ = ⌈cc.B * Lam + Chit * Lam + 1⌉ := by
          rw [Int.ceil_add_one]
        _ ≤ ⌈cc.Cexec * Lam⌉ := Int.ceil_mono hcoeffLam
    rw [hMexec]
    dsimp only [R]
    omega
  obtain ⟨r0, hRr0, hr0Raw, hr0M, hhistoryRaw, hdriftRaw⟩ :=
    initData.law P E Psi K source inferInstance hstat hunit hdag jdag Mexec
      hwin Yaux hYaux R hjR (by simpa only [← hLamEq] using hroom)
  have hjr0 : jdag ≤ r0 := hjR.trans hRr0
  have hr0 : (r0 : ℝ) ≤ (jdag : ℝ) + cc.CR * Lam := by
    have hBceil := Int.ceil_lt_add_one (cc.B * Lam)
    have hCR : cc.CR = cc.B + Chit + 1 := by
      rw [cc.CR_eq, checkpointCoefficient_eq]
    dsimp only [R] at hr0Raw
    rw [← hLamEq] at hr0Raw
    push_cast at hr0Raw hBceil
    rw [hCR]
    have hLamOne : 1 ≤ Lam := hLam
    linarith only [hr0Raw, hBceil, hLamOne]
  obtain ⟨CdQ, -, hmomentC, hlogC⟩ :=
    Initialization.exists_initialization_constant d hd g
  have hIup : initIdentityConst E ≤ 24 * aspectRatio E :=
    Initialization.initIdentityConst_le
      (Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag)
  obtain ⟨hqone, -, -, -, hraw⟩ :=
    Initialization.identity_clause_of_initIdentityConst_le hstat hg hdag hwin hYaux
      hIup hmomentC hlogC
  have hq : IsRoundedGrid jdag (1 : Mat d) := by
    simpa only [hqone] using
      (Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hwin Matrix.PosDef.one)
  have hfin : ∀ j : ℤ, jdag ≤ j → j ≤ r0 →
      HasFiniteAdaptedMean P (1 : Mat d) j := by
    intro j hj hjr
    simpa only [hqone] using
      (Initialization.finite_and_posDef_of_admissible hwin hYaux Matrix.PosDef.one
        (Initialization.identity_admissible_index hwin hj (hjr.trans hr0M))).1
  have hpos : ∀ j : ℤ, jdag ≤ j → j ≤ r0 →
      Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) j) := by
    intro j hj hjr
    simpa only [hqone] using
      (Initialization.finite_and_posDef_of_admissible hwin hYaux Matrix.PosDef.one
        (Initialization.identity_admissible_index hwin hj (hjr.trans hr0M))).2
  have hmom : ∀ j : ℤ, jdag ≤ j → j ≤ r0 →
      centeredMoment P (initExpQ d g : ℝ) (1 : Mat d) j ≠ ⊤ := by
    intro j hj hjr
    have hm := (hraw j j hj le_rfl (hjr.trans hr0M)).2.2.1
    rw [hqone] at hm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  obtain ⟨-, -, -, hprofileEq, -, -, -, -, -⟩ :=
    c.portableData.law P inferInstance hstat hunit jdag (1 : Mat d) hq
      jdag r0 r0 le_rfl hjr0 le_rfl hfin hpos hmom
  have hhistoryIn : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (1 : Mat d) jdag r0 ≤ ENNReal.ofReal c.etaIn :=
    hhistoryRaw.trans (ENNReal.ofReal_le_ofReal
      (c.init_share.trans (min_le_left _ _)))
  have hhistoryReady : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (1 : Mat d) jdag r0 ≤ ENNReal.ofReal c.etaReady :=
    hhistoryRaw.trans (ENNReal.ofReal_le_ofReal
      (c.init_share.trans (min_le_right _ _)))
  have hdrift : linearDrift P (initExpRhoDr g) (1 : Mat d) jdag r0 ≤
      c.etaNew := hdriftRaw.trans c.etaInit_le
  let A0 : BlockMat d := adaptedMean P (1 : Mat d) r0
  let hcen : ℝ≥0∞ := centeredHistory P (initExpQ d g : ℝ)
    (initExpRhoMax d g) (1 : Mat d) jdag r0
  let hnl : ℝ≥0∞ := nonlinearHistory P (initExpQ d g : ℝ)
    (initExpA g) (1 : Mat d) jdag r0
  have hA0symm : IsSymmetricBlockMat A0 := by
    exact Recurrence.isSymmetricBlockMat_adaptedMean P (1 : Mat d) r0
  have hA0pd : Book.Ch02.BlockPosDef A0 := by
    exact hpos r0 hjr0 le_rfl
  have hEsharpRaw :=
    le_of_blockMatLoewnerLE
      (isSymmetricBlockMat_blockSharp hdag.refBlock_isSymm hdag.refBlock_posDef)
      hdag.refBlock_isSymm (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
  have hEsharp : fullBlockSharp (toFullBlockMat E) ≤ toFullBlockMat E := by
    rw [toFullBlockMat_blockSharp] at hEsharpRaw
    exact hEsharpRaw
  have hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jdag (initialState r0 A0 hcen hnl) := by
    refine ⟨?_, rfl, rfl, rfl, hjr0, le_rfl⟩
    simpa only [initialState] using hqone.symm
  have hfresh : FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jdag
      (initialState r0 A0 hcen hnl) := by
    refine ⟨rfl, rfl, rfl, rfl, ?_, hdrift⟩
    simpa only [initialState, stateHistory, hcen, hnl, portableHistory] using
      hhistoryIn
  have hprofile : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jdag (initialState r0 A0 hcen hnl) ≤
        ENNReal.ofReal c.etaReady := by
    simpa only [stateProfile, initialState, A0, hcen, hnl, hprofileEq] using
      hhistoryReady
  have hprojective : stateProjectiveDistance (initialState r0 A0 hcen hnl) ≤
      (2 * (d : ℝ) * Real.log 12) * Lam := by
    have hEfull := posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
    have hTpd : E.lowerRight.PosDef :=
      posDef_of_posSemidef_of_isUnit
        (posSemidef_lowerRight hdag.refBlock_isSymm hdag.refBlock_posDef)
        ((Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_det_lowerRight hdag.refBlock_posDef))
    have hstarPd : (schurSigmaStar E).PosDef := hTpd.inv
    have hform : toFullBlockMat E =
        schurBlock (schurSigma E) (schurSigmaStar E) (schurSkew E) :=
      Initialization.toFullBlockMat_eq_schurBlock hdag.refBlock_isSymm hdag.refBlock_posDef
    have hsPd : (schurSigma E).PosDef := by
      apply posDef_of_posDef_schurBlock hstarPd
      rw [← hform]
      exact hEfull
    have hspec : 0 < specBound E.lowerRight := by
      have hnorm : (0 : ℝ) < ‖E.lowerRight‖ :=
        norm_pos_iff.mpr hTpd.isUnit.ne_zero
      simpa only [specBound_eq_norm hTpd.posSemidef] using hnorm
    have hlowQ : MatLoewnerLE
        ((specBound E.lowerRight)⁻¹ • (1 : Mat d)) (schurSigmaStar E) := by
      have hscaled := matLoewnerLE_smul (inv_nonneg.mpr hspec.le)
        (matLoewnerLE_one_specBound_smul_schurSigmaStar
          hdag.refBlock_isSymm hdag.refBlock_posDef)
      simpa only [smul_smul, inv_mul_cancel₀ hspec.ne', one_smul] using hscaled
    have hlow : (specBound E.lowerRight)⁻¹ • (1 : Mat d) ≤ schurSigmaStar E :=
      Initialization.le_of_matLoewnerLE
        ((Matrix.PosSemidef.one).smul (inv_nonneg.mpr hspec.le)).isHermitian
        hstarPd.isHermitian hlowQ
    have hhighQ :=
      matLoewnerLE_schurSigma_bigLambdaRef_smul_one hdag.refBlock_posDef
    have hhigh : schurSigma E ≤ bigLambdaRef E • (1 : Mat d) :=
      Initialization.le_of_matLoewnerLE hsPd.isHermitian
        ((Matrix.PosSemidef.one).smul (bigLambdaRef_nonneg E)).isHermitian
        hhighQ
    have hbig : 0 < bigLambdaRef E := by
      have hprod : 0 < bigLambdaRef E * specBound E.lowerRight := by
        rw [← aspectRatio_eq_bigLambdaRef_mul_specBound]
        exact lt_of_lt_of_le zero_lt_one hPi
      rcases (mul_pos_iff.mp hprod) with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge hspec.le h.2)
    have hratio : bigLambdaRef E / (specBound E.lowerRight)⁻¹ ≤
        aspectRatio E := by
      rw [div_inv_eq_mul, aspectRatio_eq_bigLambdaRef_mul_specBound]
    have hupper := (hraw r0 r0 hjr0 le_rfl hr0M).2.1
    rw [hqone] at hupper
    have hAE := le_of_blockMatLoewnerLE hA0symm
      (isSymmetricBlockMat_blockScale 2 hdag.refBlock_isSymm) hupper
    rw [toFullBlockMat_blockScale] at hAE
    have hAsharp : fullBlockSharp (toFullBlockMat A0) ≤ toFullBlockMat A0 := by
      apply fullBlockSharp_le_of_blockMatLoewnerLE hA0symm hA0pd
      simpa only [A0, adaptedMean] using
        (Sharp.blockSharp_annealedBlock_le_of_nonempty
          (Recurrence.isOpenBoundedConvexDomain_adaptedCell Matrix.PosDef.one r0)
          (Recurrence.adaptedCell_nonempty (1 : Mat d) r0) (hfin r0 hjr0 le_rfl))
    have hentry := entry_projectiveRadius hd hdag.refBlock_isSymm
      hdag.refBlock_posDef hEsharp
      (posDef_toFullBlockMat hA0symm hA0pd) hAsharp
      (by norm_num : (1 : ℝ) ≤ 2) hPi hAE
      (Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag)
      hsPd hstarPd hform (inv_pos.mpr hspec) hbig hlow hhigh hratio
    have harg : 2 + (2 : ℝ) ^ 2 * aspectRatio E ≤
        4 * (2 + aspectRatio E) := by
      nlinarith only [hPi]
    have hlogArg := Real.log_le_log (by positivity : 0 < 2 + (2 : ℝ) ^ 2 *
      aspectRatio E) harg
    have hlogMul : Real.log (4 * (2 + aspectRatio E)) =
        Real.log 4 + Real.log (2 + aspectRatio E) :=
      Real.log_mul (by norm_num) (by linarith only [hPi])
    rw [hlogMul] at hlogArg
    have hlogBase : Real.log (2 + aspectRatio E) = Real.log 3 * Lam := by
      have hlog3ne : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      rw [hLamEq, Real.logb]
      field_simp [hlog3ne]
    have hlogFour : Real.log 4 ≤ Real.log 4 * Lam := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hLam (Real.log_nonneg (by norm_num))
    have hlogTwelve : Real.log 12 = Real.log 3 + Real.log 4 := by
      rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
      norm_num
    have hlogFinal : Real.log (2 + (2 : ℝ) ^ 2 * aspectRatio E) ≤
        Real.log 12 * Lam := by
      calc
        _ ≤ Real.log 4 + Real.log (2 + aspectRatio E) := hlogArg
        _ = Real.log 4 + Real.log 3 * Lam := by rw [hlogBase]
        _ ≤ Real.log 4 * Lam + Real.log 3 * Lam := add_le_add hlogFour le_rfl
        _ = Real.log 12 * Lam := by rw [hlogTwelve]; ring
    have hmul := mul_le_mul_of_nonneg_left hlogFinal (by positivity :
      0 ≤ 2 * (d : ℝ))
    simpa only [stateProjectiveDistance, initialState, canonicalMetric, mul_assoc] using
      hentry.trans hmul
  have hroot : adaptedDetRoot P (1 : Mat d) r0 ≤ 24 * aspectRatio E := by
    have hupper := (hraw r0 r0 hjr0 le_rfl hr0M).2.1
    rw [hqone] at hupper
    have hAE := le_of_blockMatLoewnerLE hA0symm
      (isSymmetricBlockMat_blockScale 2 hdag.refBlock_isSymm) hupper
    rw [toFullBlockMat_blockScale] at hAE
    have hentry := entry_detRoot_le_kappaRef hdag.refBlock_isSymm
      hdag.refBlock_posDef (posDef_toFullBlockMat hA0symm hA0pd) hEsharp
      (by norm_num : (1 : ℝ) ≤ 2) hAE
    have hkappa :=
      Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
    calc
      adaptedDetRoot P (1 : Mat d) r0 = detRoot d A0 := rfl
      _ ≤ 4 * kappaRef E := by norm_num at hentry ⊢; exact hentry
      _ ≤ 4 * (6 * aspectRatio E) :=
        mul_le_mul_of_nonneg_left hkappa (by norm_num)
      _ = 24 * aspectRatio E := by ring
  have hpotential := initialState_potential_le (c := c)
    (alphaSearch := w.alphaSearch) cc hLam
    w.alphaFresh_pos.le (le_trans (by norm_num) w.two_le_alphaX) hprofile
    hdrift hprojective
  refine ⟨r0, A0, hcen, hnl, hRr0, hr0, hr0M, hA0symm, hA0pd,
    hexact, hfresh, hprofile, hprojective, hroot, ?_⟩
  simpa only [w.alphaW_eq] using hpotential

end

end Homogenization.HighContrast.Selection
