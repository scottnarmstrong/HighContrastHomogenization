import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport2
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentDegenerate

/-!
# HC bridge II, the recent-head cell-defect package

The pointwise cell-defect step, its form with the metric nondegeneracy hypotheses
discharged, and the full `weakCellSum` half of the recent head.
-/

open Homogenization.HighContrast (CoeffSpace blockSub matSqrt matSqrt_spec normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### HELPERS.  The POINTWISE CELL-DEFECT step of the recent head:
the first of the two summands of the printed right-hand side.  The per-cell input is
`metricNormSq_blockAverage_sub_adapted_le` (`DiagonalWeakNormComparison.lean`), and
`diagonalWeak_recent_cell_bound` is the cell bound.

The identity `cellAverage_optimizerField_respCoeffMinus_sub_eq`
(`HC2b_DiagonalWeakRecentSupport.lean`) identifies the child-minus-parent optimizer
mean difference with `R D x`, where `D` is the coarse-block defect that `weakCellDefect`
normalizes and `x = (-p, q^-)` is the response load; the reflected `M_0`
metric of that vector becomes the `M_0^{-1}` quadratic form, and the matrix comparison closes
the estimate.  The lemmas below are the links between them.

The identity `cellAverage_optimizerField_respCoeffMinus_sub_eq` and its dependency chain, plus
`blockMatVecMul_blockSwap` and `blockVecDot_blockSwap_respM0`, are public in the support file
and are used directly below. -/

omit [NeZero d] in
/-- `M^{1/2}` is a genuine square root on quadratic forms.  Same proof as the private
`h4_blockSqrt_qform` of `AdaptedEnergy.lean`, which is not in this file's import closure. -/
theorem h6a_blockSqrt_qform {A : BlockMat d} (hA : (toFullBlockMat A).PosSemidef)
    (Y : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSqrt A) Y) (blockMatVecMul (blockSqrt A) Y) =
      blockVecDot Y (blockMatVecMul A Y) := by
  obtain ⟨hS, hSS⟩ := matSqrt_spec hA
  have hfull : toFullBlockMat (blockSqrt A) = matSqrt (toFullBlockMat A) := by
    simp only [blockSqrt, toFullBlockMat_ofFullBlockMat]
  have hT : (matSqrt (toFullBlockMat A))ᵀ = matSqrt (toFullBlockMat A) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hS.isHermitian.eq
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, hfull]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT,
    Matrix.mulVec_mulVec, hSS]
  exact dotProduct_comm _ _

omit [NeZero d] in
/-- The block `diag(m^{-1}, m)` is exactly the inverse of the
flattened metric block `M_0 = diag(m, m^{-1})`.  This is what lets the matrix comparison
be applied with `M = M_0`, so that its metric constant is the printed
`K_0 = |M_0^{-1/2} Ehat M_0^{-1/2}|`. -/
theorem h6a_toFullBlockMat_respM0_inv {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) :
    toFullBlockMat (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ : BlockMat d)
      = (toFullBlockMat (respM0 F))⁻¹ := by
  have hu : IsUnit (explicitCanonicalMetric F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hm.isUnit
  have hmm : (explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F = 1 := Matrix.nonsing_inv_mul _ hu
  have hmm' : explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  refine (Matrix.inv_eq_left_inv ?_).symm
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have : ∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j
          = ((explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F) i j := (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j) +
          (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) = _ from rfl]
      simp [this, hmm, Matrix.one_apply]
    | inr j =>
      simp [toFullBlockMat, respM0]
  | inr i =>
    cases b with
    | inl j =>
      simp [toFullBlockMat, respM0]
    | inr j =>
      have : ∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j
          = (explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹) i j := (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) +
          (∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j) = _ from rfl]
      simp [this, hmm', Matrix.one_apply]

omit [NeZero d] in
/-- POINTWISE CELL DEFECT.  The metric length of the reflected action `M_0^{1/2} R D x`
of a block defect `D` on a response load `x` is controlled by the metric factor
`K_0 = |M_0^{-1/2} E M_0^{-1/2}|`, the squared `E`-normalized size of `D` — which is exactly the
summand of `weakCellDefect` — and the `E`-quadratic load `x. E x = (L^-)^2`.  Composed with
`cellAverage_optimizerField_respCoeffMinus_sub_eq` this is the current-carrier form of
`metricNormSq_blockAverage_sub_adapted_le`. -/
theorem h6a_reflected_defect_metric_le {F E D : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
      ≤ ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          ‖toFullBlockMat (normalizedBlock D E)‖ ^ 2 *
          blockVecDot x (blockMatVecMul E x) := by
  rw [h6a_blockSqrt_qform hM0.posSemidef, blockVecDot_blockSwap_respM0]
  have hquad : blockVecDot (blockMatVecMul D x)
      (blockMatVecMul (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ : BlockMat d)
        (blockMatVecMul D x))
      = (toFullBlockMat D *ᵥ toFullBlockVec x) ⬝ᵥ
          (toFullBlockMat (respM0 F))⁻¹ *ᵥ (toFullBlockMat D *ᵥ toFullBlockVec x) := by
    rw [← dotProduct_toFullBlockVec]
    simp only [toFullBlockVec_blockMatVecMul]
    rw [h6a_toFullBlockMat_respM0_inv hm]
  rw [hquad]
  have hcmp := h6a_centered_metric_quadratic_le (M := toFullBlockMat (respM0 F))
    (E := toFullBlockMat E) (D := toFullBlockMat D) hM0 hE (toFullBlockVec x)
  have hN : ‖matSqrt (toFullBlockMat (respM0 F))⁻¹ * toFullBlockMat E *
        matSqrt (toFullBlockMat (respM0 F))⁻¹‖
      = ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ := by
    simp [normalizedBlock]
  have hB : ‖matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat D *
        matSqrt (toFullBlockMat E)⁻¹‖
      = ‖toFullBlockMat (normalizedBlock D E)‖ := by
    simp [normalizedBlock]
  have hx : toFullBlockVec x ⬝ᵥ toFullBlockMat E *ᵥ toFullBlockVec x
      = blockVecDot x (blockMatVecMul E x) := by
    rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
  rw [hN, hB, hx] at hcmp
  exact hcmp

/-! ## WITHOUT THE METRIC NONDEGENERACY BINDERS.
`HC2b_DiagonalWeakRecentDegenerate.lean` classifies `respM0 F` for an ARBITRARY `F`.  There are
exactly three branches, and in each of them the pointwise cell-defect bound holds with the SAME
printed constants — so the pointwise estimate can be used
with `hm` and `hM0` DISCHARGED, not assumed.  The part of the classification that concerns
`explicitCanonicalMetric` / `respM0` is settled here; the `respEhatMinus` part is NOT settled here. -/

omit [NeZero d] in
/-- The pointwise cell-defect bound holds for
EVERY `F : BlockMat d`, with no hypothesis on `explicitCanonicalMetric F` or on `respM0 F`.
* `explicitCanonicalMetric F = 0`: `blockSqrt (respM0 F)` annihilates everything, so the left
  side is `0` and the right side is a product of nonnegative factors.
* `explicitCanonicalMetric F` a unit and `respM0 F` positive semidefinite: then `respM0 F` is positive
  DEFINITE (`Matrix.PosSemidef.posDef_iff_isUnit`) and `explicitCanonicalMetric F` is too, so this is
  literally the estimate with `hm` and `hM0`.
* `explicitCanonicalMetric F` a unit and `respM0 F` not positive semidefinite: `matSqrt` falls through
  on both `respM0 F` and its inverse, so `M_0^{1/2}` acts as the identity and the
  printed metric factor is `‖Ehat‖` itself; the bound is then the matrix comparison at `M = I`. -/
theorem h6a_reflected_defect_metric_le' {F E D : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
      ≤ ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          ‖toFullBlockMat (normalizedBlock D E)‖ ^ 2 *
          blockVecDot x (blockMatVecMul E x) := by
  have hL0 : 0 ≤ blockVecDot x (blockMatVecMul E x) := by
    have hh := hE.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec x)
    simp only [star_trivial, ← toFullBlockVec_blockMatVecMul,
      dotProduct_toFullBlockVec] at hh
    exact hh
  have hRHS : 0 ≤ ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
      ‖toFullBlockMat (normalizedBlock D E)‖ ^ 2 *
      blockVecDot x (blockMatVecMul E x) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hL0
  by_cases hu : IsUnit (explicitCanonicalMetric F).det
  · by_cases hpsd : (toFullBlockMat (respM0 F)).PosSemidef
    · have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
        hpsd.posDef_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_toFullBlockMat_respM0 hu))
      have hm : (explicitCanonicalMetric F).PosDef :=
        (posSemidef_explicitCanonicalMetric_of_respM0 hpsd).posDef_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
      exact h6a_reflected_defect_metric_le hm hM0 hE x
    · have hS1 : ∀ Y : BlockVec d, blockMatVecMul (blockSqrt (respM0 F)) Y = Y := by
        intro Y
        have hfull := toFullBlockVec_blockMatVecMul (blockSqrt (respM0 F)) Y
        rw [toFullBlockMat_blockSqrt_respM0_eq_one hpsd, Matrix.one_mulVec] at hfull
        calc blockMatVecMul (blockSqrt (respM0 F)) Y
            = ofFullBlockVec
                (toFullBlockVec (blockMatVecMul (blockSqrt (respM0 F)) Y)) :=
              (ofFullBlockVec_toFullBlockVec _).symm
          _ = ofFullBlockVec (toFullBlockVec Y) := by rw [hfull]
          _ = Y := ofFullBlockVec_toFullBlockVec Y
      rw [hS1, toFullBlockMat_normalizedBlock_respM0_eq_self E
        (isUnit_det_toFullBlockMat_respM0 hu) hpsd, blockMatVecMul_blockSwap]
      have hswap : blockVecDot
            ((blockMatVecMul D x).2, (blockMatVecMul D x).1)
            ((blockMatVecMul D x).2, (blockMatVecMul D x).1)
          = blockVecDot (blockMatVecMul D x) (blockMatVecMul D x) := by
        simp only [blockVecDot]
        ring
      rw [hswap]
      have hcmp := h6a_centered_metric_quadratic_le (M := (1 : FullBlockMat d))
        (E := toFullBlockMat E) (D := toFullBlockMat D) Matrix.PosDef.one hE
        (toFullBlockVec x)
      rw [inv_one, matSqrt_one, one_mul, mul_one, Matrix.one_mulVec] at hcmp
      have hB : ‖matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat D *
            matSqrt (toFullBlockMat E)⁻¹‖
          = ‖toFullBlockMat (normalizedBlock D E)‖ := by
        simp [normalizedBlock]
      have hx : toFullBlockVec x ⬝ᵥ toFullBlockMat E *ᵥ toFullBlockVec x
          = blockVecDot x (blockMatVecMul E x) := by
        rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
      have hDx : (toFullBlockMat D *ᵥ toFullBlockVec x) ⬝ᵥ
            (toFullBlockMat D *ᵥ toFullBlockVec x)
          = blockVecDot (blockMatVecMul D x) (blockMatVecMul D x) := by
        rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
      rw [hB, hx, hDx] at hcmp
      exact hcmp
  · rw [blockMatVecMul_blockSqrt_respM0_eq_zero
      (explicitCanonicalMetric_eq_zero_of_not_isUnit hu)]
    simpa [blockVecDot, vecDot] using hRHS

omit [NeZero d] in
/-- The normalized finite-cell root-mean-square form of
the pointwise estimate; same proof, with `hm`/`hM0` discharged instead of assumed. -/
theorem h6a_reflected_defect_avsum_le' {iota : Type*} (Z : Finset iota)
    (Dfam : iota → BlockMat d) {F E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          Real.sqrt (blockVecDot x (blockMatVecMul E x)) *
          Real.sqrt ((Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, ‖toFullBlockMat (normalizedBlock (Dfam w) E)‖ ^ 2) := by
  classical
  set K : ℝ := ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ with hKdef
  set L : ℝ := blockVecDot x (blockMatVecMul E x) with hLdef
  set c : iota → ℝ := fun w => ‖toFullBlockMat (normalizedBlock (Dfam w) E)‖ with hcdef
  have hK0 : 0 ≤ K := norm_nonneg _
  have hL0 : 0 ≤ L := by
    have h := hE.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec x)
    simp only [star_trivial, ← toFullBlockVec_blockMatVecMul,
      dotProduct_toFullBlockVec] at h
    rw [hLdef]
    exact h
  have hcard : (0 : ℝ) ≤ (Z.card : ℝ)⁻¹ := by positivity
  have hS0 : 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2 :=
    mul_nonneg hcard (Finset.sum_nonneg fun w _ => sq_nonneg (c w))
  have hsum : ∑ w ∈ Z,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
      ≤ ∑ w ∈ Z, K * c w ^ 2 * L :=
    Finset.sum_le_sum fun w _ => h6a_reflected_defect_metric_le' hE x
  have hpull : ∑ w ∈ Z, K * c w ^ 2 * L = (K * L) * ∑ w ∈ Z, c w ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hmain : (Z.card : ℝ)⁻¹ *
      ∑ w ∈ Z,
        blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
      ≤ K * L * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2) := by
    calc (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, _ ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, K * c w ^ 2 * L :=
          mul_le_mul_of_nonneg_left hsum hcard
      _ = K * L * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2) := by rw [hpull]; ring
  calc Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, _)
      ≤ Real.sqrt (K * L * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2)) := Real.sqrt_le_sqrt hmain
    _ = Real.sqrt K * Real.sqrt L *
          Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2) := by
        rw [Real.sqrt_mul (mul_nonneg hK0 hL0), Real.sqrt_mul hK0]

omit [NeZero d] in
/-- `weakCellDefect` form of the normalized finite-cell root-mean-square estimate. -/
theorem h6a_weakCellDefect_avsum_le' (q : Mat d) (t : ℤ) (n : ℕ) (b : CoeffField d)
    {F E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) x)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) x))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          Real.sqrt (blockVecDot x (blockMatVecMul E x)) *
          weakCellDefect q t n E b :=
  h6a_reflected_defect_avsum_le' (triadicIndexBox d n)
    (fun w => blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
      (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) hE x

omit [NeZero d] in
/-! ## THE `weakCellSum` HALF OF THE RECENT HEAD.
With the identity `cellAverage_optimizerField_respCoeffMinus_sub_eq`
(`HC2b_DiagonalWeakRecentSupport.lean`) available, the
child-cell mean defect is EXACTLY the reflected coarse-block defect action that
the pointwise estimates bound, at the response load `x^- = (-p, q^-)` (`AdaptedDefs.lean`).
The associated estimates are `diagonalWeak_recent_cell_bound`
(`DiagonalWeakNormRecentCell.lean`) and the first summand of
`diagonalWeak_recent_scale_decomposition_le` (`DiagonalWeakNormRecentDecomposition.lean`). -/

/-- The `weakCellSum` half, at one depth.  The normalized finite-cell root-mean-square
of the depth-`n` CHILD-OPTIMIZER mean defects, measured in `M_0`, is bounded by
`sqrt K_0 * L^- * weakCellDefect q t n Ehat a_-`, with constant `1` against the printed `16`. -/
theorem h6a_childMean_defect_avsum_le
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (V : (w : Fin d → ℤ) →
      ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a))
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ *
          Real.sqrt (respLsqMinus P jStar F t e) *
          weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
            (respCoeffMinus F a) := by
  have hstep : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
        = blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffMinus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffMinus F a)))
                  (respxMinus P jStar F t e))))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffMinus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffMinus F a)))
                  (respxMinus P jStar F t e)))) := by
    intro w _
    simp only [respCell]
    rw [cellAverage_optimizerField_respCoeffMinus_sub_eq (respGrid jStar F) hgrid t
      (t - (n : ℤ)) w F a (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) (V w).isMaximizer u hu]
    rfl
  rw [Finset.sum_congr rfl hstep]
  exact h6a_weakCellDefect_avsum_le' (respGrid jStar F) t n (respCoeffMinus F a) hE
    (respxMinus P jStar F t e)

/-- THE `weakCellSum` HALF OF THE RECENT HEAD, all depths.  Choosing the child
maximizers simultaneously and summing the one-depth estimate against the printed `3^{-n/2}`
weights over the window `n <= H` produces EXACTLY `weakCellSum`, with constant `1` against the
printed `16`.  The first summand of `diagonalWeak_recent_scale_decomposition_le`
(`DiagonalWeakNormRecentDecomposition.lean`) is the corresponding estimate. -/
theorem h6a_weakCellSum_half_le
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ *
            Real.sqrt (respLsqMinus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
              (respCoeffMinus F a) := by
  obtain ⟨V⟩ := h6a_nonempty_childMaximizerFamily (respGrid jStar F) hgrid t F a
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
  refine ⟨V, ?_⟩
  set K : ℝ :=
    Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ with hK
  set L : ℝ := Real.sqrt (respLsqMinus P jStar F t e) with hL
  have hterm : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) *
          Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffMinus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffMinus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
        ≤ K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by
    intro n _
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
    have hcell := h6a_childMean_defect_avsum_le P jStar F t e hgrid a n u hu (V n) hE
    calc (3 : ℝ) ^ (-((n : ℝ) / 2)) * _
        ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (K * L *
              weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by
          exact mul_le_mul_of_nonneg_left hcell hw
      _ = K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by ring
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [weakCellSum, Finset.mul_sum]
end

end Homogenization.HighContrast.Multiscale
