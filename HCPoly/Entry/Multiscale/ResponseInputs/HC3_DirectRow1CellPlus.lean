import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Glue
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscRow
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The terminal-optimizer replacement row on the carriers of the cutoff estimate

The first error row of `p.response.transfer` is stated on the concrete objects that the cutoff
estimate produces: the cutoff half-energy of a terminal optimizer minus the terminal response,
integrated against the law.  The pathwise identification of the defect with the `(φ - 1)`-weighted
optimizer energy, the oscillation split of that energy over the aligned cells of the coarse scale,
and the subcell comparison of half-energy with subcell response are the three inputs, taken in the
shape in which the modules that prove them state them.  Given those, the expectation of the defect
is bounded by `C (τ^- + √(τ^- E[J_t^-]) + 3^{-H} E[J_t^-])` with the explicit constant
`C = max 3 (32 d² responseCutoffProfileConst)`.

Paper: `p.response.transfer`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff half-energy row on the carriers of the estimate.**  Let `uP` be a terminal
optimizer, `φ` a cutoff, and suppose the defect `cutoffHalfEnergyAux - respJ` is identified
pathwise with the `(φ - 1)`-weighted optimizer energy; suppose the weighted energy splits over the
aligned cells of the coarse scale into its cell means plus the osculation cost
`32 d² responseCutoffProfileConst 3^{-H}` times twice the terminal response; and suppose on each
subcell the half-energy and the subcell response satisfy the one-parameter comparison
`|(1/2) E - J| ≤ D + 2 √(J D)`.  With the cutoff weights averaging to `0` and bounded by `1`, with
nonnegative subcell response and deficit, and with the annealed flat deficit equal to the scale
defect `τ^-`, the expectation of the defect is at most
`max 3 (32 d² responseCutoffProfileConst) (τ^- + √(τ^- E[J_t^-]) + 3^{-H} E[J_t^-])`.  This is the
terminal-optimizer replacement row of `p.response.transfer` assembled on the carriers the cutoff
estimate uses. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hid : ∀ a, cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x))
    (hosc : ∀ a, |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
          - (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)))
    (hcmp : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
          - ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)|
        ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
          + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) *
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))))
    (hc0 : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d H,
      |volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a))
    (hD0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
    (hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hDint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hEint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P)
    (hWint : Integrable (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P)
    (hJtint : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJval : ∀ w ∈ triadicIndexBox d H,
      (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
        = ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
    (hDval : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = respTauPlus P jStar F s t e) :
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
  have hK : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hΘ : (0 : ℝ) ≤ responseCutoffProfileConst := le_of_lt responseCutoffProfileConst_pos
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ))) hΘ) h3
  have hEJdef : (∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P) = respEJPlus P jStar F t e := by
    unfold respEJPlus
    rfl
  have hcJdef : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
      = respEJPlus P jStar F t e + respTauPlus P jStar F s t e := by
    unfold respTauPlus respEJPlus
    ring
  have hglue := abs_integral_le_row1_of_parts (P := P) (n := H)
    (c := fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
    (Ecell := fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
    (J := fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a))
    (D := fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
      - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
    (Wtot := fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x))
    (Jt := fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a))
    (K := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
    (cJ := ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
    (τ := respTauPlus P jStar F s t e) (EJ := respEJPlus P jStar F t e)
    hK hosc hcmp hc0 hc1 hJ0 hD0 hJt0 hJint hDint hEint hWint hJtint hJval hDval hEJdef hcJdef
  have hτ0 : 0 ≤ respTauPlus P jStar F s t e := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  have hEJ0 : 0 ≤ respEJPlus P jStar F t e := by
    unfold respEJPlus
    exact integral_nonneg hJt0
  have h3H0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
    Real.sqrt_nonneg _
  set C : ℝ := max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) with hCdef
  have hC3 : (3 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCΘ : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst ≤ C := by
    rw [hCdef]; exact le_max_right _ _
  have hKbound : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
        * respEJPlus P jStar F t e
      ≤ C * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
    have hEq : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * respEJPlus P jStar F t e
        = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hCΘ (mul_nonneg h3H0 hEJ0)
  have hstep : (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P|
      ≤ 3 * respTauPlus P jStar F s t e
        + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJPlus P jStar F t e := by
    have h := mul_le_mul_of_nonneg_left hglue (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    calc (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P|
        ≤ (1 / 2 : ℝ) * (6 * respTauPlus P jStar F s t e
            + 4 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + 2 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
                * respEJPlus P jStar F t e) := h
      _ = 3 * respTauPlus P jStar F s t e
            + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
                * respEJPlus P jStar F t e := by ring
  have hfinal : 3 * respTauPlus P jStar F s t e
        + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJPlus P jStar F t e
      ≤ C * (respTauPlus P jStar F s t e
          + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
    have h1 : 3 * respTauPlus P jStar F s t e ≤ C * respTauPlus P jStar F s t e :=
      mul_le_mul_of_nonneg_right hC3 hτ0
    have h2 : 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        ≤ C * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
      mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ C) hsqrt0
    calc 3 * respTauPlus P jStar F s t e
          + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJPlus P jStar F t e
        ≤ C * respTauPlus P jStar F s t e
          + C * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + C * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) :=
          add_le_add (add_le_add h1 h2) hKbound
      _ = C * (respTauPlus P jStar F s t e
          + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by ring
  calc |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
      = (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P| := by
        rw [show (∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
              - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                  (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P)
            = ∫ a, (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
                scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P from
          integral_congr_ae (Filter.Eventually.of_forall hid)]
        rw [integral_const_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (1 : ℝ) / 2 by norm_num)]
    _ ≤ 3 * respTauPlus P jStar F s t e
          + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJPlus P jStar F t e := hstep
    _ ≤ C * (respTauPlus P jStar F s t e
          + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := hfinal

end

end Homogenization.HighContrast.Multiscale
