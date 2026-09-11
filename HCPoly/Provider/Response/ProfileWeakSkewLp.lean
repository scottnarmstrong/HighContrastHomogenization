/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileSkewMeasurability
import HCPoly.Provider.Response.ProfileMaximumFiniteness

/-!
# Full weak estimates after constant-skew recentering

These provider-level specializations apply the sample-generic weak estimates
to a constant-skew recentered coefficient.  The terminal reference is sheared
by the same congruence.  Almost-everywhere finiteness of the all-scale maximum
is kept explicit here for discharge by the profile finiteness argument.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The full primal weak estimate in the hatted coordinates, conditional on
the internal all-scale finiteness bridge. -/
theorem eLpNorm_profilePrimalWeakRoot_subSkew_le_of_ae_max_ne_top [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    {jStar t : ℤ} {H : ℕ} (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ))
    {m : Mat d} (hm : m.PosDef) {rho alpha : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (halpha : alpha = (1 - rho) / 2)
    (g : Mat d) (hg : IsSkewMat g) (pMinus rMinus : Vec d)
    (hfinite : ∀ᵐ a ∂P, diagonalWeakMaximum rho q t
      (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg) ≠ ⊤) :
    eLpNorm
        (profilePrimalWeakRoot m hq t (fun a ↦ a.subSkew g hg)
          pMinus rMinus
          (profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg)
            pMinus rMinus)) 2 P ≤
      (ENNReal.ofReal
            (16 * diagonalWeakMetricFactor m
                (skewBlockCongr g (adaptedMean P q t)) *
              diagonalWeakLoadMinus
                (skewBlockCongr g (adaptedMean P q t)) pMinus rMinus) *
          (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2)
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg)) 2 P +
            eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg)) 2 P) +
        ENNReal.ofReal
            (16 * diagonalWeakMetricFactor m
                (skewBlockCongr g (adaptedMean P q t)) / (2 * alpha)) *
          (profileBadEnergy P
              (fun a ↦ diagonalWeakMaximum rho q t
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg))
              (fun a ↦ diagonalWeakEnergy hq t
                (a.subSkew g hg) pMinus rMinus) +
            profileGoodEnergy P alpha H
              (fun a ↦ diagonalWeakMaximum rho q t
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg))
              (fun a ↦ diagonalWeakEnergy hq t
                (a.subSkew g hg) pMinus rMinus))) +
        ENNReal.ofReal constantSeminormCoefficient *
          profilePrimalCenterVariance P m hq t
            (fun a ↦ a.subSkew g hg) pMinus rMinus := by
  have hjt : jStar ≤ t :=
    hstart.trans (sub_le_self t (Int.natCast_nonneg H))
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t
      (hfin t hjt le_rfl)
  have hEts : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  exact eLpNorm_profilePrimalWeakRoot_sample_le hq t H hm
    (isSymmetricBlockMat_skewBlockCongr hEts)
    (blockPosDef_skewBlockCongr hEt) hrho hrho1 halpha
    (fun a ↦ a.subSkew g hg) pMinus rMinus
    (aemeasurable_diagonalWeakCellSum_subSkew hq t H (1 / 2) hEts hEt g hg)
    (aemeasurable_diagonalWeakAverageSum_subSkew hq hP hgrid hlj hfin
      hstart (1 / 2) rho g hg)
    (aemeasurable_diagonalWeakMaximum_subSkew hq hEts hEt g hg)
    (aemeasurable_diagonalWeakEnergy_subSkew hq t g hg pMinus rMinus)
    (aemeasurable_blockCellAverage_diagonalWeakState_subSkew
      hq t g hg pMinus rMinus) hfinite

/-- The full adjoint weak estimate in the hatted coordinates retains its
independent plus-oriented load. -/
theorem eLpNorm_profileAdjointWeakRoot_subSkew_le_of_ae_max_ne_top [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    {jStar t : ℤ} {H : ℕ} (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ))
    {m : Mat d} (hm : m.PosDef) {rho alpha : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (halpha : alpha = (1 - rho) / 2)
    (g : Mat d) (hg : IsSkewMat g) (pPlus rPlus : Vec d)
    (hfinite : ∀ᵐ a ∂P, diagonalWeakMaximum rho q t
      (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg) ≠ ⊤) :
    eLpNorm
        (profileAdjointWeakRoot m hq t (fun a ↦ a.subSkew g hg)
          pPlus rPlus
          (profileAdjointCenter P hq t (fun a ↦ a.subSkew g hg)
            pPlus rPlus)) 2 P ≤
      (ENNReal.ofReal
            (16 * diagonalWeakMetricFactor m
                (skewBlockCongr g (adaptedMean P q t)) *
              diagonalWeakLoadPlus
                (skewBlockCongr g (adaptedMean P q t)) pPlus rPlus) *
          (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2)
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg)) 2 P +
            eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg)) 2 P) +
        ENNReal.ofReal
            (16 * diagonalWeakMetricFactor m
                (skewBlockCongr g (adaptedMean P q t)) / (2 * alpha)) *
          (profileBadEnergy P
              (fun a ↦ diagonalWeakMaximum rho q t
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg))
              (fun a ↦ diagonalWeakAdjointEnergy hq t
                (a.subSkew g hg) pPlus rPlus) +
            profileGoodEnergy P alpha H
              (fun a ↦ diagonalWeakMaximum rho q t
                (skewBlockCongr g (adaptedMean P q t)) (a.subSkew g hg))
              (fun a ↦ diagonalWeakAdjointEnergy hq t
                (a.subSkew g hg) pPlus rPlus))) +
        ENNReal.ofReal constantSeminormCoefficient *
          profileAdjointCenterVariance P m hq t
            (fun a ↦ a.subSkew g hg) pPlus rPlus := by
  have hjt : jStar ≤ t :=
    hstart.trans (sub_le_self t (Int.natCast_nonneg H))
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t
      (hfin t hjt le_rfl)
  have hEts : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  exact eLpNorm_profileAdjointWeakRoot_sample_le hq t H hm
    (isSymmetricBlockMat_skewBlockCongr hEts)
    (blockPosDef_skewBlockCongr hEt) hrho hrho1 halpha
    (fun a ↦ a.subSkew g hg) pPlus rPlus
    (aemeasurable_diagonalWeakCellSum_subSkew hq t H (1 / 2) hEts hEt g hg)
    (aemeasurable_diagonalWeakAverageSum_subSkew hq hP hgrid hlj hfin
      hstart (1 / 2) rho g hg)
    (aemeasurable_diagonalWeakMaximum_subSkew hq hEts hEt g hg)
    (aemeasurable_diagonalWeakAdjointEnergy_subSkew hq t g hg pPlus rPlus)
    (aemeasurable_blockCellAverage_diagonalWeakAdjointState_subSkew
      hq t g hg pPlus rPlus) hfinite

/-- The primal and adjoint hatted weak estimates under the source/window
premises.  The all-scale finiteness input is derived internally. -/
theorem eLpNorm_profileWeakRoots_subSkew_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {gamma Q rhoMax rhoDr rho Cd : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {jStar M t : ℤ}
    {Y : CoeffSpace d → ℝ}
    (hCd : 1 ≤ Cd) (hgamma : gamma < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hY : IsWindowMultiplier P gamma E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef)
    (hqeq : q = roundedGrid jStar m0)
    (hgrid : IsRoundedGrid jStar q)
    {H : ℕ}
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ))
    (hcell : adaptedCell q t ⊆ centeredCube d M)
    (hbelow : ∀ k : ℤ, k < jStar → ∀ z ∈ containedCenters q k t,
      adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hQ : 0 < Q) (hrhoSource : gamma < rhoMax)
    (hYmean : ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y)
    (hYnorm : lqNorm P Q Y ≤ 2)
    (hrhoMax : rhoMax ≤ rho) (hrhoDr : 0 ≤ rhoDr)
    (hrhoDrRho : rhoDr ≤ rho)
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1)))
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {m : Mat d} (hm : m.PosDef) {alpha : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (halpha : alpha = (1 - rho) / 2)
    (h0 : Mat d) (hh0 : IsSkewMat h0)
    (pMinus rMinus pPlus rPlus : Vec d) :
    (eLpNorm
          (profilePrimalWeakRoot m (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew h0 hh0)
            pMinus rMinus
            (profilePrimalCenter P (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (fun a ↦ a.subSkew h0 hh0)
              pMinus rMinus)) 2 P ≤
        (ENNReal.ofReal
              (16 * diagonalWeakMetricFactor m
                  (skewBlockCongr h0 (adaptedMean P q t)) *
                diagonalWeakLoadMinus
                  (skewBlockCongr h0 (adaptedMean P q t)) pMinus rMinus) *
            (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2)
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0)) 2 P +
              eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0)) 2 P) +
          ENNReal.ofReal
              (16 * diagonalWeakMetricFactor m
                  (skewBlockCongr h0 (adaptedMean P q t)) / (2 * alpha)) *
            (profileBadEnergy P
                (fun a ↦ diagonalWeakMaximum rho q t
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0))
                (fun a ↦ diagonalWeakEnergy
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew h0 hh0) pMinus rMinus) +
              profileGoodEnergy P alpha H
                (fun a ↦ diagonalWeakMaximum rho q t
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0))
                (fun a ↦ diagonalWeakEnergy
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew h0 hh0) pMinus rMinus))) +
          ENNReal.ofReal constantSeminormCoefficient *
            profilePrimalCenterVariance P m
              (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (fun a ↦ a.subSkew h0 hh0) pMinus rMinus) ∧
      (eLpNorm
          (profileAdjointWeakRoot m (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew h0 hh0)
            pPlus rPlus
            (profileAdjointCenter P (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (fun a ↦ a.subSkew h0 hh0)
              pPlus rPlus)) 2 P ≤
        (ENNReal.ofReal
              (16 * diagonalWeakMetricFactor m
                  (skewBlockCongr h0 (adaptedMean P q t)) *
                diagonalWeakLoadPlus
                  (skewBlockCongr h0 (adaptedMean P q t)) pPlus rPlus) *
            (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2)
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0)) 2 P +
              eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0)) 2 P) +
          ENNReal.ofReal
              (16 * diagonalWeakMetricFactor m
                  (skewBlockCongr h0 (adaptedMean P q t)) / (2 * alpha)) *
            (profileBadEnergy P
                (fun a ↦ diagonalWeakMaximum rho q t
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0))
                (fun a ↦ diagonalWeakAdjointEnergy
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew h0 hh0) pPlus rPlus) +
              profileGoodEnergy P alpha H
                (fun a ↦ diagonalWeakMaximum rho q t
                  (skewBlockCongr h0 (adaptedMean P q t)) (a.subSkew h0 hh0))
                (fun a ↦ diagonalWeakAdjointEnergy
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew h0 hh0) pPlus rPlus))) +
          ENNReal.ofReal constantSeminormCoefficient *
            profileAdjointCenterVariance P m
              (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (fun a ↦ a.subSkew h0 hh0) pPlus rPlus) := by
  have hjt : jStar ≤ t :=
    hstart.trans (sub_le_self t (Int.natCast_nonneg H))
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t
      (hfin t hjt le_rfl)
  let hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hfinite := ae_diagonalWeakMaximum_subSkew_ne_top hCd hgamma hE hEpd
    hY hm0 hqeq hgrid hjt hcell hbelow hQ hrhoSource hYmean hYnorm
    hrhoMax hrhoDr hrhoDrRho hEt hmono h0 hh0
  constructor
  · exact eLpNorm_profilePrimalWeakRoot_subSkew_le_of_ae_max_ne_top
      hq hP hgrid le_rfl hfin hstart hm hrho hrho1 halpha h0 hh0
      pMinus rMinus hfinite
  · exact eLpNorm_profileAdjointWeakRoot_subSkew_le_of_ae_max_ne_top
      hq hP hgrid le_rfl hfin hstart hm hrho hrho1 halpha h0 hh0
      pPlus rPlus hfinite

end

end Homogenization.HighContrast.Response
