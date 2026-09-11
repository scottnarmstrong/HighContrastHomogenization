/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileDefectBounds

/-!
# Nonlinear-history bounds for the positive response defects

The scale-`s` term in the terminal nonlinear history controls the relative
mean gain.  Combined with the terminal load estimates, this gives the primal
and adjoint response-defect bounds with their independent loads.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem ofReal_mul_history_bound
    {x C F W : ℝ} {N : ℝ≥0∞} (hC : 0 ≤ C)
    (hx : x ≤ C * F) (hF : ENNReal.ofReal F ≤ ENNReal.ofReal W * N) :
    ENNReal.ofReal x ≤ ENNReal.ofReal (C * W) * N := by
  calc
    ENNReal.ofReal x ≤ ENNReal.ofReal (C * F) :=
      ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal C * ENNReal.ofReal F := ENNReal.ofReal_mul hC
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal W * N) :=
      mul_le_mul_right hF _
    _ = ENNReal.ofReal (C * W) * N := by
      rw [ENNReal.ofReal_mul hC, mul_assoc]

private theorem real_le_of_ofReal_le
    {x C : ℝ} {N : ℝ≥0∞} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hN : N ≠ ⊤) (h : ENNReal.ofReal x ≤ ENNReal.ofReal C * N) :
    x ≤ C * N.toReal := by
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN) h
  rwa [ENNReal.toReal_ofReal hx, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC] at hreal

private theorem nonlinearHistory_root_ne_top
    (P : Measure (CoeffSpace d)) (Q a : ℝ) (q : Mat d)
    (jStar t : ℤ) (hQ : 1 ≤ Q) :
    nonlinearHistory P Q a q jStar t ^ Q⁻¹ ≠ ⊤ := by
  apply ENNReal.rpow_ne_top_of_nonneg
  · exact inv_nonneg.mpr (by linarith only [hQ])
  · rw [nonlinearHistory]
    exact ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top

/-- Stationarity and aligned mean order make the primal response defect
nonnegative. -/
theorem profilePrimalResponseDefect_nonneg_of_stationary [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    0 ≤ profilePrimalResponseDefect P
      (Recurrence.posDef_of_isRoundedGrid hgrid) g hg s t p r := by
  have hmean := Recurrence.adaptedMean_le hP hgrid hls hst hints hintt
  exact profilePrimalResponseDefect_nonneg
    (Recurrence.posDef_of_isRoundedGrid hgrid) hg hints hintt hmean p r

/-- Stationarity and aligned mean order make the coefficient-transpose
response defect nonnegative. -/
theorem profileAdjointResponseDefect_nonneg_of_stationary [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    0 ≤ profileAdjointResponseDefect P
      (Recurrence.posDef_of_isRoundedGrid hgrid) g hg s t p r := by
  have hmean := Recurrence.adaptedMean_le hP hgrid hls hst hints hintt
  exact profileAdjointResponseDefect_nonneg
    (Recurrence.posDef_of_isRoundedGrid hgrid) hg hints hintt hmean p r

/-- The primal response defect is bounded by its terminal negative load and
the scale-`s` summand of the nonlinear history. -/
theorem ofReal_profilePrimalResponseDefect_le_nonlinearHistory [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {jStar s t : ℤ} {H : ℕ} {Q a : ℝ} (hQ : 1 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hjs : jStar ≤ s) (ht : t = s + (H : ℤ)) (hH : 4 ≤ H)
    (pMinus qMinus : Vec d) :
    ENNReal.ofReal
        (profilePrimalResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          g hg s t pMinus qMinus) ≤
      ENNReal.ofReal
          ((1 / 2 : ℝ) *
            diagonalWeakLoadMinus (profileRecenteredMean P q g t)
                pMinus qMinus ^ 2 *
              (3 : ℝ) ^ (a * ((H : ℝ) - 1) / Q)) *
        nonlinearHistory P Q a q jStar t ^ Q⁻¹ := by
  have hst : s ≤ t := by omega
  have hjt : jStar ≤ t := hjs.trans hst
  have hints : HasFiniteAdaptedMean P q s := hfin s hjs hst
  have hintt : HasFiniteAdaptedMean P q t := hfin t hjt le_rfl
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t hintt
  have hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s) :=
    Recurrence.adaptedMean_le hP hgrid (hlj.trans hjs) hst hints hintt
  have hstart : jStar ≤ t - (H : ℤ) := by omega
  have hHIcc : H ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hhistory := ofReal_frakH_root_le_nonlinearHistory_root
    (H := H) (j := H) (a := a) hQ hP hgrid hlj hfin hstart hHIcc
  have hsub : t - (H : ℤ) = s := by omega
  rw [hsub] at hhistory
  let C : ℝ := (1 / 2 : ℝ) *
    diagonalWeakLoadMinus (profileRecenteredMean P q g t)
      pMinus qMinus ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpoint := profilePrimalResponseDefect_le_frakH
    (Recurrence.posDef_of_isRoundedGrid hgrid) hg hQ hints hintt hEt hmean
      pMinus qMinus
  have hpoint' :
      profilePrimalResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          g hg s t pMinus qMinus ≤
        C * frakH Q (relMean P q s t) ^ Q⁻¹ := by
    simpa only [C] using hpoint
  simpa only [C] using
    (ofReal_mul_history_bound hC hpoint' hhistory)

/-- The adjoint response defect is bounded by its independent terminal positive
load and the same scale-`s` summand of the nonlinear history. -/
theorem ofReal_profileAdjointResponseDefect_le_nonlinearHistory [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {jStar s t : ℤ} {H : ℕ} {Q a : ℝ} (hQ : 1 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hjs : jStar ≤ s) (ht : t = s + (H : ℤ)) (hH : 4 ≤ H)
    (pPlus qPlus : Vec d) :
    ENNReal.ofReal
        (profileAdjointResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          g hg s t pPlus qPlus) ≤
      ENNReal.ofReal
          ((1 / 2 : ℝ) *
            diagonalWeakLoadPlus (profileRecenteredMean P q g t)
                pPlus qPlus ^ 2 *
              (3 : ℝ) ^ (a * ((H : ℝ) - 1) / Q)) *
        nonlinearHistory P Q a q jStar t ^ Q⁻¹ := by
  have hst : s ≤ t := by omega
  have hjt : jStar ≤ t := hjs.trans hst
  have hints : HasFiniteAdaptedMean P q s := hfin s hjs hst
  have hintt : HasFiniteAdaptedMean P q t := hfin t hjt le_rfl
  have hEt : BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid t hintt
  have hmean : BlockMatLoewnerLE (adaptedMean P q t)
      (adaptedMean P q s) :=
    Recurrence.adaptedMean_le hP hgrid (hlj.trans hjs) hst hints hintt
  have hstart : jStar ≤ t - (H : ℤ) := by omega
  have hHIcc : H ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hhistory := ofReal_frakH_root_le_nonlinearHistory_root
    (H := H) (j := H) (a := a) hQ hP hgrid hlj hfin hstart hHIcc
  have hsub : t - (H : ℤ) = s := by omega
  rw [hsub] at hhistory
  let C : ℝ := (1 / 2 : ℝ) *
    diagonalWeakLoadPlus (profileRecenteredMean P q g t)
      pPlus qPlus ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpoint := profileAdjointResponseDefect_le_frakH
    (Recurrence.posDef_of_isRoundedGrid hgrid) hg hQ hints hintt hEt hmean
      pPlus qPlus
  have hpoint' :
      profileAdjointResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          g hg s t pPlus qPlus ≤
        C * frakH Q (relMean P q s t) ^ Q⁻¹ := by
    simpa only [C] using hpoint
  simpa only [C] using
    (ofReal_mul_history_bound hC hpoint' hhistory)

/-- Real-valued form of the primal nonlinear-history defect bound. -/
theorem profilePrimalResponseDefect_le_nonlinearHistory [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {jStar s t : ℤ} {H : ℕ} {Q a : ℝ} (hQ : 1 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hjs : jStar ≤ s) (ht : t = s + (H : ℤ)) (hH : 4 ≤ H)
    (pMinus qMinus : Vec d) :
    profilePrimalResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
        g hg s t pMinus qMinus ≤
      (1 / 2 : ℝ) *
          diagonalWeakLoadMinus (profileRecenteredMean P q g t)
              pMinus qMinus ^ 2 *
            (3 : ℝ) ^ (a * ((H : ℝ) - 1) / Q) *
        (nonlinearHistory P Q a q jStar t ^ Q⁻¹).toReal := by
  have hst : s ≤ t := by omega
  have hjt : jStar ≤ t := hjs.trans hst
  have hints : HasFiniteAdaptedMean P q s := hfin s hjs hst
  have hintt : HasFiniteAdaptedMean P q t := hfin t hjt le_rfl
  have hdefect0 := profilePrimalResponseDefect_nonneg_of_stationary
    hg hP hgrid (hlj.trans hjs) hst hints hintt pMinus qMinus
  have hbound := ofReal_profilePrimalResponseDefect_le_nonlinearHistory
    (a := a) hg hQ hP hgrid hlj hfin hjs ht hH pMinus qMinus
  have hcoefficient : 0 ≤
      (1 / 2 : ℝ) *
        diagonalWeakLoadMinus (profileRecenteredMean P q g t)
            pMinus qMinus ^ 2 *
          (3 : ℝ) ^ (a * ((H : ℝ) - 1) / Q) := by
    positivity
  exact real_le_of_ofReal_le hdefect0 hcoefficient
    (nonlinearHistory_root_ne_top P Q a q jStar t hQ) hbound

/-- Real-valued form of the adjoint nonlinear-history defect bound, retaining
its independent positive load. -/
theorem profileAdjointResponseDefect_le_nonlinearHistory [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {g : Mat d} (hg : IsSkewMat g)
    {jStar s t : ℤ} {H : ℕ} {Q a : ℝ} (hQ : 1 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hjs : jStar ≤ s) (ht : t = s + (H : ℤ)) (hH : 4 ≤ H)
    (pPlus qPlus : Vec d) :
    profileAdjointResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
        g hg s t pPlus qPlus ≤
      (1 / 2 : ℝ) *
          diagonalWeakLoadPlus (profileRecenteredMean P q g t)
              pPlus qPlus ^ 2 *
            (3 : ℝ) ^ (a * ((H : ℝ) - 1) / Q) *
        (nonlinearHistory P Q a q jStar t ^ Q⁻¹).toReal := by
  have hst : s ≤ t := by omega
  have hjt : jStar ≤ t := hjs.trans hst
  have hints : HasFiniteAdaptedMean P q s := hfin s hjs hst
  have hintt : HasFiniteAdaptedMean P q t := hfin t hjt le_rfl
  have hdefect0 := profileAdjointResponseDefect_nonneg_of_stationary
    hg hP hgrid (hlj.trans hjs) hst hints hintt pPlus qPlus
  have hbound := ofReal_profileAdjointResponseDefect_le_nonlinearHistory
    (a := a) hg hQ hP hgrid hlj hfin hjs ht hH pPlus qPlus
  have hcoefficient : 0 ≤
      (1 / 2 : ℝ) *
        diagonalWeakLoadPlus (profileRecenteredMean P q g t)
            pPlus qPlus ^ 2 *
          (3 : ℝ) ^ (a * ((H : ℝ) - 1) / Q) := by
    positivity
  exact real_le_of_ofReal_le hdefect0 hcoefficient
    (nonlinearHistory_root_ne_top P Q a q jStar t hQ) hbound

end

end Homogenization.HighContrast.Response
