import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCellEnergy

/-!
# The analytic per-scale input, reduced to its two analytic facts

## What this file does and does not do

`h6a_recentHead_actual_le` (`HC2b_DiagonalWeakRecentAssembly.lean`) has exactly ONE
remaining hypothesis, its `hscale`: the analytic per-scale bound on the average-defect family.
That bound is `diagonalWeak_recent_average_bound`.

Reading the proof of that theorem, its content splits cleanly in two:

* an **algebraic spine** — per-cell bound, average, Cauchy–Schwarz-free `√` algebra — which is
  pure real arithmetic over a `Finset`; and
* two **analytic inputs**, `metricBlockNormSq_recent_difference_le` and
  `diagonalWeak_recent_difference_energy_le`, which are PDE facts about the doubled response
  space.

**This file proves the spine and states the two analytic inputs as explicit hypotheses in
this tree's own language.**  It does NOT prove those two inputs; their root
`energy_map_metric_le` rests on
`doubledResponseValue_le` / `doubledResponseValue_zero_left_eq` and
on the reflection-order layer (`blockSharp`, 444 lines plus its
`VariationalIdentities.lean` base of 323), none of which exists in this tree OR in the
`CoarseGraining` dependency.

What is gained is nonetheless the substance of the bound: after this file, the per-scale bound
is reduced to TWO named inequalities, stated on this tree's carriers, whose
conjunction discharges `hscale` mechanically.

Nothing is imported from an external development and no file is copied; the spine is stated on
this tree's inline `√(|Z|⁻¹ ∑ ⟪·,·⟫)` carrier, which is
what `weakCellSum`, `h6a_besovSeminorm_head_tail_le` and `hscale` all spell.
-/

open Homogenization.HighContrast (CoeffSpace normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The algebraic spine of the per-scale input**, on an arbitrary index `Finset`.

This is `diagonalWeak_recent_average_bound`
with its two analytic inputs abstracted into the hypotheses `hcell` and `henergy`, and with
`blockAvsumL2` unfolded to this tree's inline `√(|Z|⁻¹ ∑ ⟪·,·⟫)`.

`hcell` is the per-cell bound assembled from `metricBlockNormSq_recent_difference_le`
together with the all-scale-maximum bound on the response size; `henergy` is
`diagonalWeak_recent_difference_energy_le`.  Everything after them is real arithmetic —
`Finset.sum_le_sum`, a nonnegative rescaling, and `√(c²x) = c√x`. -/
theorem h6a_scaleInput_spine_le {iota : Type*} (Z : Finset iota) (R : BlockMat d)
    (Δ : iota → BlockVec d) (G : iota → ℝ) (K B L D : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hcell : ∀ w ∈ Z,
      blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w)) ≤ (K * B) ^ 2 * G w)
    (henergy : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, G w ≤ 2 * L ^ 2 * D) :
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w)))
      ≤ Real.sqrt 2 * K * B * L * Real.sqrt D := by
  have hcard : (0 : ℝ) ≤ (Z.card : ℝ)⁻¹ := by positivity
  -- the averaged per-cell bound
  have hsum : (Z.card : ℝ)⁻¹ *
      ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w))
      ≤ (K * B) ^ 2 * (2 * L ^ 2 * D) := by
    have hstep : ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w))
        ≤ ∑ w ∈ Z, (K * B) ^ 2 * G w := Finset.sum_le_sum hcell
    calc
      (Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w))
          ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (K * B) ^ 2 * G w :=
        mul_le_mul_of_nonneg_left hstep hcard
      _ = (K * B) ^ 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, G w) := by
        rw [← Finset.mul_sum]; ring
      _ ≤ (K * B) ^ 2 * (2 * L ^ 2 * D) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg (K * B))
  -- the right-hand side is the square root of that bound
  have hC0 : 0 ≤ Real.sqrt 2 * K * B * L * Real.sqrt D := by positivity
  have hradicand : (K * B) ^ 2 * (2 * L ^ 2 * D)
      = (Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2 := by
    have hroot2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hrootD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
    calc
      (K * B) ^ 2 * (2 * L ^ 2 * D)
          = Real.sqrt 2 ^ 2 * (K * B * L) ^ 2 * Real.sqrt D ^ 2 := by
        rw [hroot2, hrootD]; ring
      _ = (Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2 := by ring
  calc
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z, blockVecDot (blockMatVecMul R (Δ w)) (blockMatVecMul R (Δ w)))
        ≤ Real.sqrt ((K * B) ^ 2 * (2 * L ^ 2 * D)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2) := by rw [hradicand]
    _ = Real.sqrt 2 * K * B * L * Real.sqrt D := Real.sqrt_sq hC0

/-! ## The spine at the exact shape of `hscale`. -/

omit [NeZero d] in
/-- **The per-scale input, reduced to its two analytic inputs.**  This is `h6a_scaleInput_spine_le`
instantiated at exactly the shape of the remaining hypothesis `hscale`
(`h6a_recentHead_actual_le`, `HC2b_DiagonalWeakRecentAssembly.lean`): the index set is
`triadicIndexBox d n`, the root is `blockSqrt (respM0 F)`, and the four scalars are the printed
ones —

* `K = √(blockSpecBound (normalizedBlock Ê⁻ M₀))`, the `diagonalWeakMetricFactor m E`;
* `B = 1 + √(respAllScaleMax) · 3^{ρn/2}`, the all-scale-maximum factor;
* `L = √(respLsqMinus)`, the `diagonalWeakLoadMinus E p r`;
* `D = ‖weakAverageDefect …‖`, the `blockSize (diagonalWeakAverageDefect …) (blockIdentity d)`.

The field family `Y` is left abstract: `h6a_recentHead_actual_le` instantiates it at
`Y w = fun x => optimizerField b u x - optimizerField b (V n w) x`, which matches definitionally.

**The two hypotheses are precisely the two analytic inputs**, in this tree's language:

* `hcell` is `metricBlockNormSq_recent_difference_le`
  composed with the response-size bound `blockSize (adaptedResponse …) E ≤ B²`, which is
  derived from `sqrt_blockSize_adaptedResponse_le_of_maximum_finite`;
* `henergy` is `diagonalWeak_recent_difference_energy_le`.

Neither is proved in this tree.  What this theorem establishes is that NOTHING ELSE is needed:
given those two, `hscale` follows mechanically, and with it the entire first printed
summand of `diagonalWeakNorm_primal_le`. -/
theorem h6a_scaleInput_of_analytic
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (a : CoeffSpace d) (n : ℕ)
    (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ)
    (hLsq : 0 ≤ respLsqMinus P jStar F t e)
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 * G w)
    (henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
      ≤ 2 * respLsqMinus P jStar F t e
          * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
              (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqMinus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖ := by
  have hB : (0 : ℝ) ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) :=
    add_nonneg zero_le_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hLsq' : Real.sqrt (respLsqMinus P jStar F t e) ^ 2 = respLsqMinus P jStar F t e :=
    Real.sq_sqrt hLsq
  refine h6a_scaleInput_spine_le (triadicIndexBox d n) (blockSqrt (respM0 F))
    (fun w => cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)) G
    _ _ _ _ (Real.sqrt_nonneg _) hB (Real.sqrt_nonneg _) (norm_nonneg _) hcell ?_
  rw [hLsq']
  exact henergy

end

end Homogenization.HighContrast.Multiscale
