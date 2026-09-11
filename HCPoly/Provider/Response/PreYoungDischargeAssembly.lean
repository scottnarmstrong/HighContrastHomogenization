/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.PreYoungPrimalRows
import HCPoly.Provider.Response.PreYoungAdjointRows

/-!
# Unconditional pre-Young response families

A common dimension-dependent constant controls the primal and adjoint compact
pre-Young estimates for every admissible source window.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

/-- There is a common dimension-dependent constant for the primal and adjoint
compact pre-Young response families. -/
theorem exists_pre_young_response_families (d : ℕ) [NeZero d] :
    ∃ Cpre : ℝ, 1 ≤ Cpre ∧
      ∀ {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P],
      ∀ (_hstat : HCPoly.Frozen.IsStationaryLaw P),
      ∀ {gamma : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K Cd : ℝ}
        {jStar M : ℤ} {Y : CoeffSpace d → ℝ},
      ∀ (_hY : IsWindowMultiplier P gamma E Psi K Cd jStar M Y),
      ∀ {m0 q : Mat d},
      ∀ (_hm0 : m0.PosDef) (_hqeq : q = roundedGrid jStar m0)
        (hgrid : IsRoundedGrid jStar q),
      ∀ {s t : ℤ},
      ∀ (_hjs : jStar ≤ s) (H : ℕ) (_ht : t = s + (H : ℤ)),
      ∀ (_hbelow : ∀ k : ℤ, k < jStar → ∀ v : ℤ,
        v = s ∨ v = t → ∀ z ∈ containedCenters q k v,
          adaptedCellTranslate q k z ⊆ centeredCube d M),
      ∀ (_hblocks : ∀ k : ℤ, jStar ≤ k → k ≤ t →
        HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k)),
      ((∀ Cresp, Cpre ≤ Cresp →
        ∀ (h0 : {h : Mat d // IsSkewMat h}) (p r : Vec d),
          let hq := Recurrence.posDef_of_isRoundedGrid hgrid
          let X := profilePrimalCenter P hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let tau := profilePrimalResponseDefect P hq h0
            h0.property s t p r
          let EJ := ∫ a, responseJ (adaptedDomain hq t)
            ((a.subSkew h0 h0.property).coeffOn
              (adaptedDomain hq t)) p r ∂P
          let row := profilePrimalHattedEarlierRow P q h0 s X.1 X.2
          let weak := profilePrimalWeakQuantity P m0 hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
            (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hq t))
              (centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
            (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).coeffOn (adaptedDomain hq t))
              (centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
          ENNReal.ofReal |Jtilde| ≤
            ENNReal.ofReal Cresp * ENNReal.ofReal (Real.sqrt tau) *
              (ENNReal.ofReal (Real.sqrt tau) +
                ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp *
              ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
              ENNReal.ofReal (Real.sqrt EJ) *
                (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp * weak) ∧
      (∀ Cresp, Cpre ≤ Cresp →
        ∀ (h0 : {h : Mat d // IsSkewMat h}) (p r : Vec d),
          let hq := Recurrence.posDef_of_isRoundedGrid hgrid
          let X := profileAdjointCenter P hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let tau := profileAdjointResponseDefect P hq h0
            h0.property s t p r
          let EJ := ∫ a, responseJ (adaptedDomain hq t)
            ((a.subSkew h0 h0.property).transpose.coeffOn
              (adaptedDomain hq t)) p r ∂P
          let row := profileAdjointHattedEarlierRow P q h0 s X.1 X.2
          let weak := profileAdjointWeakQuantity P m0 hq t
            (fun a ↦ a.subSkew h0 h0.property) p r
          let Jtilde := EJ - (1 / 2 : ℝ) * vecDot
            (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).transpose.coeffOn
                (adaptedDomain hq t))
              (centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
            (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
              ((a.subSkew h0 h0.property).transpose.coeffOn
                (adaptedDomain hq t))
              (centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew h0 h0.property) p r) i ∂P)
          ENNReal.ofReal |Jtilde| ≤
            ENNReal.ofReal Cresp * ENNReal.ofReal (Real.sqrt tau) *
              (ENNReal.ofReal (Real.sqrt tau) +
                ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp *
              ENNReal.ofReal ((3 : ℝ) ^ (-(H : ℝ))) *
              ENNReal.ofReal (Real.sqrt EJ) *
                (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
            ENNReal.ofReal Cresp * weak)) := by
  obtain ⟨Cpre, hCpre, hcut, hcomponent, hfour, hsqrtTwo⟩ :=
    exists_one_le_pre_young_constant d (preYoungComponentCoefficient d)
  refine ⟨Cpre, hCpre, ?_⟩
  intro P _ hstat gamma E Psi K Cd jStar M Y hY m0 q hm0 hqeq hgrid
    s t hjs H ht hbelow hblocks
  subst q
  have hst : s ≤ t := by omega
  have hints := (hblocks s hjs hst).1
  have hjt : jStar ≤ t := hjs.trans hst
  have hintt := (hblocks t hjt le_rfl).1
  constructor
  · intro Cresp hCresp h0 p r
    have hcompact := compact_pre_young_primal_of_row_estimates
      hm0 hgrid hstat hjs H ht hints hintt h0 h0.property p r
      hCpre hcut hcomponent hfour hsqrtTwo
      (fun hweak ↦ profile_primal_cutoff_mean_rows_le
        hstat hY hm0 rfl hgrid hjs H ht hbelow hblocks
          h0 h0.property p r hweak)
    exact hcompact Cresp hCresp
  · intro Cresp hCresp h0 p r
    have hcompact := compact_pre_young_adjoint_of_row_estimates
      hm0 hgrid hstat hjs H ht hints hintt h0 h0.property p r
      hCpre hcut hcomponent hfour hsqrtTwo
      (fun hweak ↦ profile_adjoint_cutoff_mean_rows_le
        hstat hY hm0 rfl hgrid hjs H ht hbelow hblocks
          h0 h0.property p r hweak)
    exact hcompact Cresp hCresp

end

end Homogenization.HighContrast.Response
