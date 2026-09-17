import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Glue
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscRow
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The terminal-optimizer replacement row on the carriers of the cutoff estimate

This assembles the first error row of `p.response.transfer` on the same carriers the cutoff
estimate uses.  The left-hand side is the difference between the cutoff half-energy of the
terminal optimizer and the terminal response, integrated over the law of coefficients.  The three
geometric inputs — the pathwise identification of that difference with the `(φ - 1)`-weighted
optimizer energy, the oscillation split of that energy over the subdivision into the aligned
coarse cells, and the subcell comparison of the half-energy with the subcell response — enter as
hypotheses in the shape in which the modules that prove them produce them.  The conclusion is the
printed bound

`C (τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-])`

with the explicit dimensional constant `C = max 3 (32 d^2 * responseCutoffProfileConst)`.

Paper: `p.response.transfer`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal-optimizer replacement row on the cutoff carriers.**  Assume the pathwise
identification `hid` of the cutoff half-energy minus the terminal response with the
`(φ - 1)`-weighted optimizer energy; the oscillation split `hosc` of that weighted energy over the
aligned cells of the coarse scale, costing `32 d^2 responseCutoffProfileConst 3^{-H}` times twice
the terminal response; and the subcell comparison `hcmp` of half the subcell energy with the
subcell response through its nonnegative deficit.  Assume the cutoff fluctuation has mean-zero
normalized subcell means `hc0` and is bounded by `1` on each subcell `hc1`, the subcell responses
and deficits are nonnegative and integrable, the subcell responses have a common annealed value
`hJval`, and the annealed flat mean of the deficits is the scale defect `hDval`.  Then the
law-integral of the cutoff half-energy minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-]`.  This is the first error row of
`p.response.transfer` on the carriers of the cutoff estimate. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hid : ∀ a, cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x))
    (hosc : ∀ a, |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)
          - (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)))
    (hcmp : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
          - ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)|
        ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
          + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) *
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                (respqMinus P jStar F t e) (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))))
    (hc0 : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d H,
      |volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a))
    (hD0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
    (hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hDint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P)
    (hEint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P)
    (hWint : Integrable (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P)
    (hJtint : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJval : ∀ w ∈ triadicIndexBox d H,
      (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
        = ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
    (hDval : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P)
      = respTauMinus P jStar F s t e) :
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
  have hK : 0 ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) := by
    have hθ : 0 ≤ responseCutoffProfileConst := le_of_lt responseCutoffProfileConst_pos
    have h3 : 0 ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
    positivity
  have hcJ : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      = respEJMinus P jStar F t e + respTauMinus P jStar F s t e := by
    unfold respTauMinus
    ring
  have hglue : |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P|
      ≤ 6 * respTauMinus P jStar F s t e
        + 4 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
        + 2 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJMinus P jStar F t e :=
    abs_integral_le_row1_of_parts (d := d) P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      (fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a))
      (fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
      (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x))
      (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a))
      (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
      (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      (respTauMinus P jStar F s t e) (respEJMinus P jStar F t e)
      hK hosc hcmp hc0 hc1 hJ0 hD0 hJt0 hJint hDint hEint hWint hJtint hJval hDval rfl hcJ
  have hLHS : |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      = (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P| := by
    have h1 : (∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
          - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P)
        = ∫ a, (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    rw [h1, integral_const_mul, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
  have hNnonneg : 0 ≤ (((triadicIndexBox d H).card : ℝ))⁻¹ := by
    have hcard : ((triadicIndexBox d H).card : ℝ) = ((3 : ℝ) ^ H) ^ d :=
      card_triadicIndexBox H
    rw [hcard]
    positivity
  have hτ0 : 0 ≤ respTauMinus P jStar F s t e := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg hNnonneg
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  have hEJ0 : 0 ≤ respEJMinus P jStar F t e := by
    show 0 ≤ ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P
    exact integral_nonneg hJt0
  have h3H : 0 ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hC3 : (3 : ℝ) ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) :=
    le_max_left _ _
  have hCθ : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) := le_max_right _ _
  have hC2 : (2 : ℝ) ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) :=
    le_trans (by norm_num) hC3
  have h1 : 3 * respTauMinus P jStar F s t e
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) * respTauMinus P jStar F s t e :=
    mul_le_mul_of_nonneg_right hC3 hτ0
  have h2 : 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) :=
    mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)
  have h3 : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
        * respEJMinus P jStar F t e
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
    calc (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * respEJMinus P jStar F t e
        = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
            * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by ring
      _ ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
            * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) :=
          mul_le_mul_of_nonneg_right hCθ (mul_nonneg h3H hEJ0)
  have hfinal : 3 * respTauMinus P jStar F s t e
        + 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
        + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJMinus P jStar F t e
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
    calc 3 * respTauMinus P jStar F s t e
          + 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJMinus P jStar F t e
        ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) * respTauMinus P jStar F s t e
          + max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
              * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
              * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) :=
          add_le_add (add_le_add h1 h2) h3
      _ = max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by ring
  calc |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      = (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P| := hLHS
    _ ≤ (1 / 2 : ℝ) * (6 * respTauMinus P jStar F s t e
          + 4 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + 2 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJMinus P jStar F t e) :=
        mul_le_mul_of_nonneg_left hglue (by norm_num)
    _ = 3 * respTauMinus P jStar F s t e
          + 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJMinus P jStar F t e := by ring
    _ ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := hfinal

end

end Homogenization.HighContrast.Multiscale
