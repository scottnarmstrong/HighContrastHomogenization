/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileCenterIdentities
import HCPoly.Provider.Response.ConstantSkewNormalization

/-!
# Centering variance after skew recentering

The hatted optimizer average differs from its independently annealed center by
the reflected action of one centered hatted block.  Common shear congruence
then returns the bound to the portable centered maximum.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Pointwise primal centering in the hatted coordinates is controlled by the
portable centered terminal maximum. -/
theorem ofReal_sqrt_primal_subSkew_center_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {m : Mat d} (hm : m.PosDef) {q : Mat d} (hq : q.PosDef)
    {rhoMax : ℝ} {jStar t : ℤ} (hjt : jStar ≤ t)
    (hint : HasFiniteAdaptedMean P q t) (hEt : BlockPosDef (adaptedMean P q t))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (a : CoeffSpace d) :
    ENNReal.ofReal (Real.sqrt (metricBlockNormSq m
        (blockCellAverage (adaptedCell q t)
            (diagonalWeakState hq t (a.subSkew g hg) p r) -
          profilePrimalCenter P hq t (fun b ↦ b.subSkew g hg) p r))) ≤
      ENNReal.ofReal
          (diagonalWeakMetricFactor m
              (skewBlockCongr g (adaptedMean P q t)) *
            diagonalWeakLoadMinus
              (skewBlockCongr g (adaptedMean P q t)) p r) *
        profileCenteredMaximum P rhoMax q jStar t a := by
  let E := adaptedMean P q t
  let A := coarseBlock (adaptedCell q t) a
  let Ehat := skewBlockCongr g E
  let Ahat := skewBlockCongr g A
  have hA : IsSymmetricBlockMat A := isSymmetricBlockMat_coarseBlock _ a
  have hE : IsSymmetricBlockMat E := Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hAhat : IsSymmetricBlockMat Ahat :=
    isSymmetricBlockMat_skewBlockCongr (g := g) hA
  have hEhat : IsSymmetricBlockMat Ehat :=
    isSymmetricBlockMat_skewBlockCongr (g := g) hE
  have hEhatpd : BlockPosDef Ehat :=
    blockPosDef_skewBlockCongr (g := g) hEt
  have hsample : coarseBlock (adaptedCell q t) (a.subSkew g hg) = Ahat := by
    simpa only [adaptedDomain_carrier, Ahat, A] using
      coarseBlock_subSkew (adaptedDomain hq t) a g hg
  have hreal := sqrt_metricBlockNormSq_responseAverage_sub_le hm
    hAhat hEhat hEhatpd p r
  rw [← blockSub_skewBlockCongr, blockSize_skewBlockCongr] at hreal
  rw [blockCellAverage_diagonalWeakState_eq_response hq t (a.subSkew g hg) p r,
    hsample, profilePrimalCenter_subSkew_eq hq t hint g hg p r]
  calc
    ENNReal.ofReal (Real.sqrt (metricBlockNormSq m
        ((blockMatVecMul (blockR d)
              (blockMatVecMul Ahat ((-p, r) : BlockVec d)) +
            ((-p, r) : BlockVec d)) -
          (blockMatVecMul (blockR d)
              (blockMatVecMul Ehat ((-p, r) : BlockVec d)) +
            ((-p, r) : BlockVec d))))) ≤
        ENNReal.ofReal
          (diagonalWeakMetricFactor m Ehat *
            diagonalWeakLoadMinus Ehat p r * blockSize (blockSub A E) E) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal
          (diagonalWeakMetricFactor m Ehat *
            diagonalWeakLoadMinus Ehat p r) *
        ENNReal.ofReal (blockSize (blockSub A E) E) := by
      rw [ENNReal.ofReal_mul (mul_nonneg
        (diagonalWeakMetricFactor_nonneg m Ehat)
        (diagonalWeakLoadMinus_nonneg Ehat p r))]
    _ ≤ ENNReal.ofReal
          (diagonalWeakMetricFactor m Ehat *
            diagonalWeakLoadMinus Ehat p r) *
        profileCenteredMaximum P rhoMax q jStar t a := by
      exact mul_le_mul_of_nonneg_left
        (PortableHistory.ofReal_blockSize_le_centeredSup hq hjt a) (zero_le _)

/-- Pointwise adjoint centering in the hatted coordinates has the same
portable maximum and its independent plus load. -/
theorem ofReal_sqrt_adjoint_subSkew_center_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {m : Mat d} (hm : m.PosDef) {q : Mat d} (hq : q.PosDef)
    {rhoMax : ℝ} {jStar t : ℤ} (hjt : jStar ≤ t)
    (hint : HasFiniteAdaptedMean P q t) (hEt : BlockPosDef (adaptedMean P q t))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (a : CoeffSpace d) :
    ENNReal.ofReal (Real.sqrt (metricBlockNormSq m
        (blockCellAverage (adaptedCell q t)
            (diagonalWeakAdjointState hq t (a.subSkew g hg) p r) -
          profileAdjointCenter P hq t (fun b ↦ b.subSkew g hg) p r))) ≤
      ENNReal.ofReal
          (diagonalWeakMetricFactor m
              (skewBlockCongr g (adaptedMean P q t)) *
            diagonalWeakLoadPlus
              (skewBlockCongr g (adaptedMean P q t)) p r) *
        profileCenteredMaximum P rhoMax q jStar t a := by
  let E := adaptedMean P q t
  let A := coarseBlock (adaptedCell q t) a
  let Ehat := skewBlockCongr g E
  let Ahat := skewBlockCongr g A
  let Ead := blockMatMul (blockDiag 1 (-1))
    (blockMatMul Ehat (blockDiag 1 (-1)))
  let Aad := blockMatMul (blockDiag 1 (-1))
    (blockMatMul Ahat (blockDiag 1 (-1)))
  have hA : IsSymmetricBlockMat A := isSymmetricBlockMat_coarseBlock _ a
  have hE : IsSymmetricBlockMat E := Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hAhat : IsSymmetricBlockMat Ahat :=
    isSymmetricBlockMat_skewBlockCongr (g := g) hA
  have hEhat : IsSymmetricBlockMat Ehat :=
    isSymmetricBlockMat_skewBlockCongr (g := g) hE
  have hAad : IsSymmetricBlockMat Aad := isSymmetricBlockMat_adjointSign_congr hAhat
  have hEad : IsSymmetricBlockMat Ead := isSymmetricBlockMat_adjointSign_congr hEhat
  have hEhatpd : BlockPosDef Ehat := blockPosDef_skewBlockCongr (g := g) hEt
  have hEadpd : BlockPosDef Ead := blockPosDef_adjointSign_congr hEhatpd
  have hsample : coarseBlock (adaptedCell q t) (a.subSkew g hg) = Ahat := by
    simpa only [adaptedDomain_carrier, Ahat, A] using
      coarseBlock_subSkew (adaptedDomain hq t) a g hg
  have htranspose :
      coarseBlock (adaptedCell q t) (a.subSkew g hg).transpose = Aad := by
    have hraw := coarseBlock_transpose (a.subSkew g hg) (adaptedDomain hq t)
    simpa only [adaptedDomain_carrier, hsample, Aad] using hraw
  have hreal := sqrt_metricBlockNormSq_responseAverage_sub_le hm
    hAad hEad hEadpd p r
  rw [← blockSub_adjointSign_congr, blockSize_adjointSign_congr,
    diagonalWeakMetricFactor_adjoint, diagonalWeakLoadMinus_adjoint,
    ← blockSub_skewBlockCongr, blockSize_skewBlockCongr] at hreal
  rw [diagonalWeakAdjointState_eq,
    blockCellAverage_diagonalWeakState_eq_response hq t
      (a.subSkew g hg).transpose p r,
    htranspose, profileAdjointCenter_subSkew_eq hq t hint g hg p r]
  calc
    ENNReal.ofReal (Real.sqrt (metricBlockNormSq m
        ((blockMatVecMul (blockR d)
              (blockMatVecMul Aad ((-p, r) : BlockVec d)) +
            ((-p, r) : BlockVec d)) -
          (blockMatVecMul (blockR d)
              (blockMatVecMul Ead ((-p, r) : BlockVec d)) +
            ((-p, r) : BlockVec d))))) ≤
        ENNReal.ofReal
          (diagonalWeakMetricFactor m Ehat *
            diagonalWeakLoadPlus Ehat p r * blockSize (blockSub A E) E) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal
          (diagonalWeakMetricFactor m Ehat * diagonalWeakLoadPlus Ehat p r) *
        ENNReal.ofReal (blockSize (blockSub A E) E) := by
      rw [ENNReal.ofReal_mul (mul_nonneg
        (diagonalWeakMetricFactor_nonneg m Ehat)
        (diagonalWeakLoadPlus_nonneg Ehat p r))]
    _ ≤ ENNReal.ofReal
          (diagonalWeakMetricFactor m Ehat * diagonalWeakLoadPlus Ehat p r) *
        profileCenteredMaximum P rhoMax q jStar t a := by
      exact mul_le_mul_of_nonneg_left
        (PortableHistory.ofReal_blockSize_le_centeredSup hq hjt a) (zero_le _)

/-- The primal hatted annealed-centering variance has the portable history
bound. -/
theorem profilePrimalCenterVariance_subSkew_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q rhoMax : ℝ} (hQ : 2 ≤ Q) {m : Mat d} (hm : m.PosDef)
    {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} (hjt : jStar ≤ t)
    (hint : HasFiniteAdaptedMean P q t) (hEt : BlockPosDef (adaptedMean P q t))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    profilePrimalCenterVariance P m hq t (fun a ↦ a.subSkew g hg) p r ≤
      ENNReal.ofReal
          (diagonalWeakMetricFactor m
              (skewBlockCongr g (adaptedMean P q t)) *
            diagonalWeakLoadMinus
              (skewBlockCongr g (adaptedMean P q t)) p r) *
        centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ := by
  let Z := profileCenteredMaximum P rhoMax q jStar t
  let C := diagonalWeakMetricFactor m (skewBlockCongr g (adaptedMean P q t)) *
    diagonalWeakLoadMinus (skewBlockCongr g (adaptedMean P q t)) p r
  have hZ : AEStronglyMeasurable Z P :=
    (aemeasurable_profileCenteredMaximum hq hEt).aestronglyMeasurable
  calc
    profilePrimalCenterVariance P m hq t (fun a ↦ a.subSkew g hg) p r ≤
        eLpNorm (fun a ↦ ENNReal.ofReal C * Z a) 2 P := by
      apply eLpNorm_mono_enorm
      intro a
      simpa only [enorm_eq_self, C, Z] using
        ofReal_sqrt_primal_subSkew_center_le_profile
          hm hq hjt hint hEt g hg p r a
    _ ≤ ENNReal.ofReal C * eLpNorm Z 2 P :=
      eLpNorm_ofReal_mul_le hZ C 2
    _ ≤ ENNReal.ofReal C *
        centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ := by
      exact mul_right_mono (eLpNorm_two_profileCenteredMaximum_le hq hQ hEt)

/-- The adjoint hatted annealed-centering variance has the portable history
bound with its independent plus load. -/
theorem profileAdjointCenterVariance_subSkew_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q rhoMax : ℝ} (hQ : 2 ≤ Q) {m : Mat d} (hm : m.PosDef)
    {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} (hjt : jStar ≤ t)
    (hint : HasFiniteAdaptedMean P q t) (hEt : BlockPosDef (adaptedMean P q t))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    profileAdjointCenterVariance P m hq t (fun a ↦ a.subSkew g hg) p r ≤
      ENNReal.ofReal
          (diagonalWeakMetricFactor m
              (skewBlockCongr g (adaptedMean P q t)) *
            diagonalWeakLoadPlus
              (skewBlockCongr g (adaptedMean P q t)) p r) *
        centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ := by
  let Z := profileCenteredMaximum P rhoMax q jStar t
  let C := diagonalWeakMetricFactor m (skewBlockCongr g (adaptedMean P q t)) *
    diagonalWeakLoadPlus (skewBlockCongr g (adaptedMean P q t)) p r
  have hZ : AEStronglyMeasurable Z P :=
    (aemeasurable_profileCenteredMaximum hq hEt).aestronglyMeasurable
  calc
    profileAdjointCenterVariance P m hq t (fun a ↦ a.subSkew g hg) p r ≤
        eLpNorm (fun a ↦ ENNReal.ofReal C * Z a) 2 P := by
      apply eLpNorm_mono_enorm
      intro a
      simpa only [enorm_eq_self, C, Z] using
        ofReal_sqrt_adjoint_subSkew_center_le_profile
          hm hq hjt hint hEt g hg p r a
    _ ≤ ENNReal.ofReal C * eLpNorm Z 2 P :=
      eLpNorm_ofReal_mul_le hZ C 2
    _ ≤ ENNReal.ofReal C *
        centeredHistory P Q rhoMax q jStar t ^ Q⁻¹ := by
      exact mul_right_mono (eLpNorm_two_profileCenteredMaximum_le hq hQ hEt)

end

end Homogenization.HighContrast.Response
