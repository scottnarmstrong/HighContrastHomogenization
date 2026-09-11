/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.PreYoungRemainingPhysicalRows
import HCPoly.Provider.Response.PreYoungAdjointAssembly

/-!
# Adjoint cutoff-mean component rows

The independently transposed recent-difference and cutoff-oscillation estimates
combine into the two boundary rows used by the compact adjoint pre-Young
estimate.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The transposed recent-difference row and the physical cutoff-oscillation
row give the two adjoint cutoff-mean component bounds. -/
theorem profile_adjoint_cutoff_mean_rows_le_of_recent_defect [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {gamma : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K Cd : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P gamma E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef) (hqeq : q = roundedGrid jStar m0)
    (hgrid : IsRoundedGrid jStar q)
    {s t : ℤ} (hjs : jStar ≤ s) (H : ℕ) (ht : t = s + (H : ℤ))
    (hbelow : ∀ k : ℤ, k < jStar → ∀ v : ℤ,
      v = s ∨ v = t → ∀ z ∈ containedCenters q k v,
        adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hblocks : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profileAdjointWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤)
    (hdefects :
      let hq := Recurrence.posDef_of_isRoundedGrid hgrid
      let X := profileAdjointCenter P hq t (fun a ↦ a.subSkew g hg) p r
      let tau := profileAdjointResponseDefect P hq g hg s t p r
      let cut := adaptedPreYoungCutoff q hq t
      let child := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦
        diagonalWeakChildState hq s w
        (a.subSkew g hg).transpose p r
      let parent := fun (a : CoeffSpace d) ↦
        diagonalWeakState hq t (a.subSkew g hg).transpose p r
      ENNReal.ofReal
          |avsum (alignedIndex q s t) (fun w ↦
            (1 - volumeAverage (adaptedCellAt q s w) cut) *
              ∑ i, X.2 i *
                ((∫ a, toFullBlockVec
                    (blockCellAverage (adaptedCellAt q s w) (child w a))
                      (Sum.inl i) ∂P) -
                  ∫ a, toFullBlockVec
                    (blockCellAverage (adaptedCellAt q s w) (parent a))
                      (Sum.inl i) ∂P))| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadFlux (profileHattedAdjointBlock g (adaptedMean P q s)) X.2) ∧
      ENNReal.ofReal
          |avsum (alignedIndex q s t) (fun w ↦
            (1 - volumeAverage (adaptedCellAt q s w) cut) *
              ∑ i, X.1 i *
                ((∫ a, toFullBlockVec
                    (blockCellAverage (adaptedCellAt q s w) (child w a))
                      (Sum.inr i) ∂P) -
                  ∫ a, toFullBlockVec
                    (blockCellAverage (adaptedCellAt q s w) (parent a))
                      (Sum.inr i) ∂P))| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadGradient
            (profileHattedAdjointBlock g (adaptedMean P q s)) X.1)) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let X := profileAdjointCenter P hq t (fun a ↦ a.subSkew g hg) p r
    let tau := profileAdjointResponseDefect P hq g hg s t p r
    let EJ := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r ∂P
    let gain := preYoungComponentCoefficient d *
      (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ
    let cut := adaptedPreYoungCutoff q hq t
    ENNReal.ofReal
        |vecDot X.2 (profileAdjointCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).1| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadFlux (profileHattedAdjointBlock g (adaptedMean P q s)) X.2) +
          ENNReal.ofReal gain *
            profileAdjointHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) ∧
      ENNReal.ofReal
        |vecDot X.1 (profileAdjointCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).2| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadGradient (profileHattedAdjointBlock g (adaptedMean P q s)) X.1) +
          ENNReal.ofReal gain *
            profileAdjointHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let X := profileAdjointCenter P hq t (fun a ↦ a.subSkew g hg) p r
  let tau := profileAdjointResponseDefect P hq g hg s t p r
  let EJ := ∫ a, responseJ (adaptedDomain hq t)
    ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r ∂P
  let gain := preYoungComponentCoefficient d *
    (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ
  let cut := adaptedPreYoungCutoff q hq t
  let Pcen := X.1
  let Qcen := X.2
  let child := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦ diagonalWeakChildState hq s w
    (a.subSkew g hg).transpose p r
  let parent := fun (a : CoeffSpace d) ↦
    diagonalWeakState hq t (a.subSkew g hg).transpose p r
  let defectGrad := avsum (alignedIndex q s t) (fun w ↦
    (1 - volumeAverage (adaptedCellAt q s w) cut) * ∑ i, Qcen i *
      ((∫ a, toFullBlockVec
          (blockCellAverage (adaptedCellAt q s w) (child w a)) (Sum.inl i) ∂P) -
        ∫ a, toFullBlockVec
          (blockCellAverage (adaptedCellAt q s w) (parent a)) (Sum.inl i) ∂P))
  let defectFlux := avsum (alignedIndex q s t) (fun w ↦
    (1 - volumeAverage (adaptedCellAt q s w) cut) * ∑ i, Pcen i *
      ((∫ a, toFullBlockVec
          (blockCellAverage (adaptedCellAt q s w) (child w a)) (Sum.inr i) ∂P) -
        ∫ a, toFullBlockVec
          (blockCellAverage (adaptedCellAt q s w) (parent a)) (Sum.inr i) ∂P))
  let oscGrad := avsum (alignedIndex q s t) (fun w ↦
    ∑ i, Qcen i * ∫ a, volumeAverage (adaptedCellAt q s w) (fun x ↦
      (cut x - volumeAverage (adaptedCellAt q s w) cut) *
        toFullBlockVec (parent a x) (Sum.inl i)) ∂P)
  let oscFlux := avsum (alignedIndex q s t) (fun w ↦
    ∑ i, Pcen i * ∫ a, volumeAverage (adaptedCellAt q s w) (fun x ↦
      (cut x - volumeAverage (adaptedCellAt q s w) cut) *
        toFullBlockVec (parent a x) (Sum.inr i)) ∂P)
  have hst : s ≤ t := by omega
  have hints := (hblocks s hjs hst).1
  have hread := integrable_adjoint_adaptedFiveTermSplit_readouts
    hq hm0 hst g hg p r hweak
  have hsplitGrad0 := vecDot_profileAdjointCutoffMean_fst_eq_defect_add_oscillation
    hstat hgrid hjs hst hints g hg p r Qcen hread
  have hsplitFlux0 := vecDot_profileAdjointCutoffMean_snd_eq_defect_add_oscillation
    hstat hgrid hjs hst hints g hg p r Pcen hread
  have hsplitGrad : vecDot Qcen
      (profileAdjointCutoffMean P hq t (fun a ↦ a.subSkew g hg) cut p r).1 =
      defectGrad + oscGrad := by
    simpa only [hq, cut, child, parent, defectGrad, oscGrad] using hsplitGrad0
  have hsplitFlux : vecDot Pcen
      (profileAdjointCutoffMean P hq t (fun a ↦ a.subSkew g hg) cut p r).2 =
      defectFlux + oscFlux := by
    simpa only [hq, cut, child, parent, defectFlux, oscFlux] using hsplitFlux0
  have hdefectGrad : ENNReal.ofReal |defectGrad| ≤
      ENNReal.ofReal (Real.sqrt (4 * tau) *
        profileSchurLoadFlux (profileHattedAdjointBlock g (adaptedMean P q s)) Qcen) := by
    simpa only [hq, tau, cut, child, parent, defectGrad] using hdefects.1
  have hdefectFlux : ENNReal.ofReal |defectFlux| ≤
      ENNReal.ofReal (Real.sqrt (4 * tau) *
        profileSchurLoadGradient (profileHattedAdjointBlock g (adaptedMean P q s)) Pcen) := by
    simpa only [hq, tau, cut, child, parent, defectFlux] using hdefects.2
  have hoscGrad0 := of_real_abs_adjoint_gradient_cutoff_oscillation_row_le
    hstat hY hm0 hqeq hgrid hjs hst hbelow hblocks
      g hg p r Pcen Qcen hweak
  have hoscFlux0 := of_real_abs_adjoint_flux_cutoff_oscillation_row_le
    hstat hY hm0 hqeq hgrid hjs hst hbelow hblocks
      g hg p r Pcen Qcen hweak
  have hgap : (t : ℝ) - (s : ℝ) = (H : ℝ) := by
    rw [ht]
    push_cast
    ring
  have hcoeff : preYoungRowCoefficient d * (3 : ℝ) ^ (-(H : ℝ)) *
      Real.sqrt EJ ≤ preYoungComponentCoefficient d *
        (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (preYoungRowCoefficient_le_component d)
        (Real.rpow_nonneg (by norm_num) _)) (Real.sqrt_nonneg _)
  have hgain : ENNReal.ofReal
      (preYoungRowCoefficient d * (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ) ≤
      ENNReal.ofReal gain := by
    exact ENNReal.ofReal_le_ofReal (by simpa only [gain] using hcoeff)
  have hoscGrad : ENNReal.ofReal |oscGrad| ≤ ENNReal.ofReal gain *
      profileAdjointHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
    have h0 := hoscGrad0
    rw [hgap] at h0
    have h1 : ENNReal.ofReal |oscGrad| ≤
        ENNReal.ofReal
            (preYoungRowCoefficient d * (3 : ℝ) ^ (-(H : ℝ)) *
              Real.sqrt EJ) *
          profileAdjointHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
      simpa only [hq, EJ, cut, parent, oscGrad] using h0
    refine h1.trans ?_
    gcongr
  have hoscFlux : ENNReal.ofReal |oscFlux| ≤ ENNReal.ofReal gain *
      profileAdjointHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
    have h0 := hoscFlux0
    rw [hgap] at h0
    have h1 : ENNReal.ofReal |oscFlux| ≤
        ENNReal.ofReal
            (preYoungRowCoefficient d * (3 : ℝ) ^ (-(H : ℝ)) *
              Real.sqrt EJ) *
          profileAdjointHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
      simpa only [hq, EJ, cut, parent, oscFlux] using h0
    refine h1.trans ?_
    gcongr
  constructor
  · exact ofReal_abs_le_add_of_component_bounds
      (ofReal_abs_le_add_of_eq_add hsplitGrad) hdefectGrad hoscGrad
  · exact ofReal_abs_le_add_of_component_bounds
      (ofReal_abs_le_add_of_eq_add hsplitFlux) hdefectFlux hoscFlux

end

end Homogenization.HighContrast.Response

