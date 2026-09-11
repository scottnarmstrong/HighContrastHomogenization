/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.CenteredResponseTrace

/-!
# The centered-response trace bound

Positivity bounds the spectral norm of the normalized corrected response block
by its trace.  The exact basis-sum identity then compares that trace with the
supremum of the combined centered response over Euclidean unit vectors.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory Set

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The combined centered responses on the Euclidean unit sphere are bounded
above. -/
theorem bddAbove_centeredResponseTraceValue
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    BddAbove
      ((fun e : Vec d => centeredResponseTraceValue P U S SStar K e) ''
        {e : Vec d | e ⬝ᵥ e = 1}) := by
  refine ⟨‖centeredResponseTraceMatrix S SStar K‖, ?_⟩
  intro x hx
  rcases hx with ⟨e, he, rfl⟩
  change e ⬝ᵥ e = 1 at he
  change centeredResponseTraceValue P U S SStar K e ≤ _
  rw [centeredResponseTraceValue_eq_quadratic U hint hS hStar hE]
  have hbound := dotProduct_mulVec_le_norm_mul
    (centeredResponseTraceMatrix S SStar K) e
  rw [he, mul_one] at hbound
  exact hbound

/-- The corrected trace estimate. -/
theorem centeredResponse_trace_bound
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    ‖matSqrt SStar⁻¹ * centeredResponseBlock S SStar K *
          matSqrt SStar⁻¹ - 1‖ ≤
      2 * (d : ℝ) *
        sSup
          ((fun e : Vec d => centeredResponseTraceValue P U S SStar K e) ''
            {e : Vec d | e ⬝ᵥ e = 1}) := by
  let X : Mat d := centeredResponseX S SStar
  let Y : Mat d := centeredResponseY SStar K
  have horder := annealed_schurStar_le_schur U hint hS hStar hE
  have hX : X.PosSemidef := centeredResponseX_posSemidef hStar horder
  have hY : Y.PosSemidef := centeredResponseY_posSemidef hStar K
  have hXY : (X + Y).PosSemidef := hX.add hY
  have hnormTrace : ‖X + Y‖ ≤ Matrix.trace (X + Y) := by
    exact norm_le_of_le_smul_one hXY hXY.trace_nonneg
      (Recurrence.le_trace_smul_one hXY)
  have htraceWide :
      Matrix.trace (X + Y) ≤
        2 * (Matrix.trace X + 2 * Matrix.trace Y) := by
    rw [Matrix.trace_add]
    have hx0 : 0 ≤ Matrix.trace X := hX.trace_nonneg
    have hy0 : 0 ≤ Matrix.trace Y := hY.trace_nonneg
    linarith only [hx0, hy0]
  have hnormSum :
      ‖X + Y‖ ≤
        2 * ∑ i : Fin d, centeredResponseTraceValue P U S SStar K
          (Pi.single i (1 : ℝ)) := by
    rw [sum_centeredResponseTraceValue U hint hS hStar hE]
    exact hnormTrace.trans htraceWide
  let R : ℝ := sSup
    ((fun e : Vec d => centeredResponseTraceValue P U S SStar K e) ''
      {e : Vec d | e ⬝ᵥ e = 1})
  have hbdd := bddAbove_centeredResponseTraceValue U hint hS hStar hE
  have hbasis (i : Fin d) :
      centeredResponseTraceValue P U S SStar K (Pi.single i (1 : ℝ)) ≤ R := by
    apply le_csSup hbdd
    refine ⟨Pi.single i (1 : ℝ), ?_, rfl⟩
    simp [dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  have hsum :
      (∑ i : Fin d, centeredResponseTraceValue P U S SStar K
        (Pi.single i (1 : ℝ))) ≤ (d : ℝ) * R := by
    calc
      (∑ i : Fin d, centeredResponseTraceValue P U S SStar K
          (Pi.single i (1 : ℝ))) ≤ ∑ _i : Fin d, R :=
        Finset.sum_le_sum fun i _ => hbasis i
      _ = (d : ℝ) * R := by simp
  have hfinal := hnormSum.trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
  rw [normalized_centeredResponseBlock_eq_X_add_Y]
  change ‖X + Y‖ ≤ _
  change ‖X + Y‖ ≤ 2 * (d : ℝ) * R
  simpa only [mul_assoc] using hfinal

end

end Homogenization.HighContrast.Response
