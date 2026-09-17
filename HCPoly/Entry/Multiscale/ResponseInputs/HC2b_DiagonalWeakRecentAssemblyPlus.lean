import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentCellSumPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakAvSumPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCongrPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakScaleInputPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentAssembly

/-!
# The recent head of the cell-average estimate, adjoint sign

The weak-norm estimate for the response controls the recent head of the cell-average defect for
two reflected coefficients: the recentred field `a_- = a - g` with response matrix
`E_-^t = respEhatMinus`, and the adjoint field `a_+ = a^t + g` with adjoint response matrix
`E_+^t = respEhatPlus`.  This file assembles the adjoint head: the one-sided `weakCellSum` half,
the `weakAverageSum` half, their composition into the printed summand, and the reduction of the
per-scale analytic input through the two energy facts.  Every statement is the adjoint-sign
counterpart of its recentred-sign original; only the carrier changes, and no constant or binder
order moves.
-/

open Homogenization.HighContrast (CoeffSpace normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The `weakCellSum` half of the recent-head cell-average estimate for the adjoint sample
`a_+ = respCoeffPlus F a`, stated against the metric factor the estimate prints.  The spectral
bound `sqrt (blockSpecBound (normalizedBlock E_+ M_0))` replaces the operator norm delivered by
the reflected-defect comparison; on positive definite `E_+` and `M_0` the two coincide.  This is
the cell half of the response weak-norm estimate. -/
theorem h6a_weakCellSum_half_specBound_le_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
              (respCoeffPlus F a) := by
  obtain ⟨V, hV⟩ := h6a_weakCellSum_half_le_plus P jStar F t e hgrid a H u hu hE
  exact ⟨V, by rwa [h6a_respK0_specBound_eq_norm_plus P jStar F t hE hM0]⟩

/-- The two-halves composition for the adjoint sample with the child-maximizer family produced
before the per-scale analytic constraint: the same maximizer family then serves every admissible
per-scale family `A`.  The maximizers are chosen from the cell half alone, so moving `exists V`
outside `forall A` is a binder reorder and strictly strengthens the statement. -/
theorem h6a_recentHead_halves_forall_le_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      ∀ A : ℕ → ℝ,
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqPlus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))) + A n)
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a) +
              weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
  classical
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) with hK
  set L : ℝ := Real.sqrt (respLsqPlus P jStar F t e) with hL
  have hK0 : (0 : ℝ) ≤ K := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Real.sqrt_nonneg _
  obtain ⟨V, hV⟩ := h6a_weakCellSum_half_specBound_le_plus P jStar F t e hgrid a H u hu hE hM0
  refine ⟨V, fun A hscale => ?_⟩
  have hav := h6a_weakAverageSum_half_le_plus (K := K) (L := L) P γ hγ jStar H F t a hK0 hL0 A hE
    hgood hscale
  have hcs0 : (0 : ℝ) ≤ weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
      (respCoeffPlus F a) := weakCellSum_nonneg _ _ _ _ _
  have has0 : (0 : ℝ) ≤ weakAverageSum (respGrid jStar F) t H (respRho γ)
      (respEhatPlus P jStar F t) (respCoeffPlus F a) := weakAverageSum_nonneg _ _ _ _ _ _
  have hsplit : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))) + A n)
        = (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u))))
          + (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n := fun n _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  nlinarith [hV, hav, hcs0, has0, mul_nonneg hK0 hL0]

/-- The recent head of the cell-average estimate for the adjoint sample, against the actual parent
optimizer rather than a family of child maximizers.  The child maximizers are eliminated by the
recent-scale decomposition and the per-scale family is restricted to the explicit average-defect
family, leaving the analytic per-scale input as the only remaining hypothesis. -/
theorem h6a_recentHead_actual_le_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffPlus F a) u x -
                          optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffPlus F a) u x -
                          optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))) ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqPlus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a) +
              weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
  classical
  obtain ⟨V, hV⟩ := h6a_recentHead_halves_forall_le_plus P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood
  refine ⟨V, fun h1v h2v hscale => ?_⟩
  refine le_trans ?_ (hV _ hscale)
  exact h6a_recentHead_scale_decomposition_box_le (respGrid jStar F) t H (blockSqrt (respM0 F))
    (optimizerField (respCoeffPlus F a) u)
    (fun n w => optimizerField (respCoeffPlus F a)
      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction))
    (cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))
    h1u h2u h1v h2v

/-- The recent head for the adjoint sample reduced to the two analytic energy facts.  The per-scale
input is discharged through `h6a_scaleInput_of_analytic_plus`: a per-cell energy family `G` bounds
the quadratic defect cellwise and its cell average is controlled by the response load
`respLsqPlus` times the averaged recent-defect size.  The side condition `0 <= respLsqPlus` is
discharged from the positive definiteness of the adjoint response matrix.  This is the adjoint
counterpart of the reduction of the recent-head estimate to the energy-map and difference-energy
bounds. -/
theorem h6a_recentHead_actual_of_analytic_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, ∃ G : (Fin d → ℤ) → ℝ,
        (∀ w ∈ triadicIndexBox d n,
          blockVecDot
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffPlus F a) u x -
                    optimizerField (respCoeffPlus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffPlus F a) u x -
                    optimizerField (respCoeffPlus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
            ≤ (Real.sqrt
                  (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
                * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                    * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 * G w) ∧
        ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
          ≤ 2 * respLsqPlus P jStar F t e
              * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
                  (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a) +
              weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
  classical
  -- The former side hypothesis `hLsq`, now discharged from `hE`.
  have hLsq : 0 ≤ respLsqPlus P jStar F t e := by
    rw [respLsqPlus]
    exact h6a_blockVecDot_nonneg_of_posSemidef _ hE.posSemidef _
  obtain ⟨V, hV⟩ := h6a_recentHead_actual_le_plus P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood h1u h2u
  refine ⟨V, fun h1v h2v hin => hV h1v h2v (fun n => ?_)⟩
  obtain ⟨G, hcell, henergy⟩ := hin n
  exact h6a_scaleInput_of_analytic_plus P γ jStar F t e a n
    (fun w x => optimizerField (respCoeffPlus F a) u x -
      optimizerField (respCoeffPlus F a)
        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)
    G hLsq hcell henergy

end

end Homogenization.HighContrast.Multiscale
