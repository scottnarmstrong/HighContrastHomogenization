/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseScalarClosure

/-!
# Compact pre-Young insertion at the Schur loads

The two carried compact estimates are specialized to the independently
centered primal and adjoint responses and discharged by the calibrated
defect, energy, hatted-row, and weak bounds.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory Set

open scoped ENNReal Matrix

noncomputable section

/-- The skew coordinate of a Schur block is an admissible profile gauge. -/
theorem is_skew_mat_response_skew {d : ℕ} (K : Mat d) :
    IsSkewMat (responseSkew K) := by
  rw [responseSkew, IsSkewMat, ← conjTranspose_eq_matTranspose,
    Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  rw [show Kᴴ - K = -(K - Kᴴ) by abel, smul_neg]

/-- The two literal compact pre-Young estimates imply the response supremum
bound used by the deterministic endgame. -/
theorem centered_response_sup_le_of_compact_pre_young
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d) {S SStar K : Mat d}
    {C expo T A L R kappa omega : ℝ}
    (hC : 0 ≤ C) (hexpo : 0 ≤ expo)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hkappa : 1 ≤ kappa)
    (homega : omega = 2 * C *
      (T + Real.sqrt (T * A) + Real.sqrt (T * L) +
        expo * (A + Real.sqrt (A * L)) + R ^ 2))
    (tauMinus tauPlus EJMinus EJPlus : Vec d → ℝ)
    (rowMinus rowPlus weakMinus weakPlus : Vec d → ℝ≥0∞)
    (hpreYoungMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |centeredResponse P U (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e -
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (tauMinus e)) *
          (ENNReal.ofReal (Real.sqrt (tauMinus e)) +
            ENNReal.ofReal (Real.sqrt (EJMinus e)) +
              rowMinus e ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * ENNReal.ofReal expo *
          ENNReal.ofReal (Real.sqrt (EJMinus e)) *
            (ENNReal.ofReal (Real.sqrt (EJMinus e)) +
              rowMinus e ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * weakMinus e)
    (hpreYoungPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |centeredAdjointResponse P U
            (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e +
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (tauPlus e)) *
          (ENNReal.ofReal (Real.sqrt (tauPlus e)) +
            ENNReal.ofReal (Real.sqrt (EJPlus e)) +
              rowPlus e ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * ENNReal.ofReal expo *
          ENNReal.ofReal (Real.sqrt (EJPlus e)) *
            (ENNReal.ofReal (Real.sqrt (EJPlus e)) +
              rowPlus e ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * weakPlus e)
    (htauMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      tauMinus e ≤ T * Real.sqrt kappa)
    (htauPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      tauPlus e ≤ T * Real.sqrt kappa)
    (hEJMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      EJMinus e ≤ A * Real.sqrt kappa)
    (hEJPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      EJPlus e ≤ A * Real.sqrt kappa)
    (hrowMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      rowMinus e ≤ ENNReal.ofReal (L * kappa ^ (3 / 2 : ℝ)))
    (hrowPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      rowPlus e ≤ ENNReal.ofReal (L * kappa ^ (3 / 2 : ℝ)))
    (hweakMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      weakMinus e ≤ ENNReal.ofReal (R ^ 2 * kappa))
    (hweakPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      weakPlus e ≤ ENNReal.ofReal (R ^ 2 * kappa)) :
    sSup
        ((fun e : Vec d ↦
            |centeredResponse P U (centeredResponseLoadP S SStar K e)
                (centeredResponseLoadQ S SStar K e -
                  responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| +
              |centeredAdjointResponse P U
                (centeredResponseLoadP S SStar K e)
                (centeredResponseLoadQ S SStar K e +
                  responseSkew K *ᵥ centeredResponseLoadP S SStar K e)|) ''
          {e : Vec d | e ⬝ᵥ e = 1}) ≤ omega * kappa := by
  let scalar := T + Real.sqrt (T * A) + Real.sqrt (T * L) +
    expo * (A + Real.sqrt (A * L)) + R ^ 2
  let preMinus : Vec d → ℝ≥0∞ := fun e ↦
    ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (tauMinus e)) *
        (ENNReal.ofReal (Real.sqrt (tauMinus e)) +
          ENNReal.ofReal (Real.sqrt (EJMinus e)) +
            rowMinus e ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * ENNReal.ofReal expo *
        ENNReal.ofReal (Real.sqrt (EJMinus e)) *
          (ENNReal.ofReal (Real.sqrt (EJMinus e)) +
            rowMinus e ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * weakMinus e
  let prePlus : Vec d → ℝ≥0∞ := fun e ↦
    ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (tauPlus e)) *
        (ENNReal.ofReal (Real.sqrt (tauPlus e)) +
          ENNReal.ofReal (Real.sqrt (EJPlus e)) +
            rowPlus e ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * ENNReal.ofReal expo *
        ENNReal.ofReal (Real.sqrt (EJPlus e)) *
          (ENNReal.ofReal (Real.sqrt (EJPlus e)) +
            rowPlus e ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * weakPlus e
  have hscalar : 0 ≤ scalar := by
    dsimp only [scalar]
    positivity
  have hkappa0 : 0 ≤ kappa := le_trans zero_le_one hkappa
  have homegaKappa : 0 ≤ omega * kappa := by
    rw [homega]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hscalar) hkappa0
  apply centered_response_sup_le_of_pre_young U homegaKappa preMinus prePlus
  · intro e he
    exact hpreYoungMinus e he
  · intro e he
    exact hpreYoungPlus e he
  · intro e he
    have hminus := literal_compact_pre_young_allocation hC hexpo hT hA hL
      hkappa (htauMinus e he) (hEJMinus e he) (hrowMinus e he)
      (hweakMinus e he)
    have hplus := literal_compact_pre_young_allocation hC hexpo hT hA hL
      hkappa (htauPlus e he) (hEJPlus e he) (hrowPlus e he)
      (hweakPlus e he)
    exact two_half_allocations hC hscalar hkappa0
      (by simpa only [scalar] using homega) hminus hplus

end

end Homogenization.HighContrast.Response
