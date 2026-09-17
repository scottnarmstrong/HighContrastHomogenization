import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectBoxProd
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectDescStat
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsHeadExpect
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsBlockIntegral

/-!
# The annealed head of the descendant layer of the source load

Step ζ of the cutoff-mean row of `p.response.transfer` at descendant depth `n`.  The terminal
cell is cut into the `3^{(H+n)d}` aligned cells of generation `s - n`; on each of them the
pathwise full-dual pairing produces the head `√(Y₁ · 𝐀(V; a_-).upperLeft Y₁) +
√(Y₂ · 𝐀(V; b).lowerRight Y₂)`, and its annealed flat average over all `3^{(H+n)d}` cells is at
most the depth-`n` layer of `respSourceLoad`, i.e. the flat average over the `3^{nd}` descendants
of ONE scale-`s` cell of the same head read on the ANNEALED block.

The estimate is the two-term expectation bound `integral_sq_sqrt_add_sqrt_le` applied cell by
cell, the identification of each pathwise quadratic form with the annealed one
(`integral_vecDot_coarseBlock_upperLeft`/`…_lowerRight`), the grouped-digit decomposition of the
index box `sum_triadicIndexBox_add`, and the stationarity identity
`annealedBlockOf_descendant_respCoeffMinus_eq`/`…_Plus_eq`, which makes the summand independent
of the outer index and collapses the outer sum.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The descendant layer bound, uniformly in the recentred coefficient family.**  For an
arbitrary family `b` of coefficient fields, if the pathwise head is integrable cell by cell and
the annealed block of a descendant cell depends only on the inner index, then the annealed flat
average of the squared pathwise head over the depth-`(H + n)` index box is at most the depth-`n`
layer of the source load read on the annealed block. -/
private theorem integral_avsum_sq_head_descendant_le_aux {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (b : CoeffSpace d → CoeffField d) (H n : ℕ) (s : ℤ) (Y : BlockVec d)
    (hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).upperLeft Y.1)) P)
    (hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).lowerRight Y.2)) P)
    (hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).upperLeft i k) P)
    (hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).lowerRight i k) P)
    (hUL0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).upperLeft Y.1))
    (hLR0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).lowerRight Y.2))
    (hcross : ∀ W : Fin d → ℤ, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (b a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (b a)).lowerRight Y.2))) P)
    (hsq : ∀ W : Fin d → ℤ, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).lowerRight Y.2))) ^ 2) P)
    (hdesc : ∀ w z : Fin d → ℤ,
      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
          (fun i => 3 ^ n * w i + z i)) b).upperLeft
        = (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
            b).upperLeft ∧
      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
          (fun i => 3 ^ n * w i + z i)) b).lowerRight
        = (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
            b).lowerRight) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (b a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).lowerRight Y.2))) ^ 2 := by
  have hterm : ∀ W : Fin d → ℤ,
      (∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).lowerRight Y.2))) ^ 2 ∂P)
        ≤ (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                b).lowerRight Y.2))) ^ 2 := by
    intro W
    have hhead := integral_sq_sqrt_add_sqrt_le P (hUL W) (hLR W) (hUL0 W) (hLR0 W)
      (hcross W) (hsq W)
    have hfbar := integral_vecDot_coarseBlock_upperLeft P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) b Y.1 (hULe W)
    have hgbar := integral_vecDot_coarseBlock_lowerRight P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) b Y.2 (hLRe W)
    rw [hfbar, hgbar] at hhead
    exact hhead
  have hsum_bound :
      (∑ W ∈ triadicIndexBox d (H + n),
          ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).lowerRight Y.2))) ^ 2 ∂P)
        ≤ ∑ W ∈ triadicIndexBox d (H + n),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    b).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    b).lowerRight Y.2))) ^ 2 :=
    Finset.sum_le_sum (fun W _ => hterm W)
  have hLHS :
      (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
          ∑ W ∈ triadicIndexBox d (H + n),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).lowerRight Y.2))) ^ 2 ∂P)
        = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
          ∑ W ∈ triadicIndexBox d (H + n),
            ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).lowerRight Y.2))) ^ 2 ∂P := by
    rw [integral_const_mul,
      integral_finsetSum (triadicIndexBox d (H + n)) (fun W _ => hsq W)]
  have hcHn_inv_nonneg : 0 ≤ (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ := by
    have hpos : (0 : ℝ) < ((triadicIndexBox d (H + n)).card : ℝ) := by
      rw [card_triadicIndexBox (H + n)]
      positivity
    exact inv_nonneg.mpr (le_of_lt hpos)
  have hreindex :
      (∑ W ∈ triadicIndexBox d (H + n),
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  b).lowerRight Y.2))) ^ 2)
        = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                      (fun i => 3 ^ n * w i + z i)) b).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                      (fun i => 3 ^ n * w i + z i)) b).lowerRight Y.2))) ^ 2 :=
    sum_triadicIndexBox_add (d := d) H n
      (fun W => (Real.sqrt (vecDot Y.1 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              b).lowerRight Y.2))) ^ 2)
  have hdesc_sum :
      (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                    (fun i => 3 ^ n * w i + z i)) b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                    (fun i => 3 ^ n * w i + z i)) b).lowerRight Y.2))) ^ 2)
        = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                    b).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                    b).lowerRight Y.2))) ^ 2 := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [(hdesc w z).1, (hdesc w z).2]
  have hcollapse :
      (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).lowerRight Y.2))) ^ 2)
        = ((triadicIndexBox d H).card : ℝ) *
            ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).lowerRight Y.2))) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((triadicIndexBox d (H + n)).card : ℝ))
      = (((triadicIndexBox d H).card : ℝ)) * (((triadicIndexBox d n).card : ℝ)) := by
    rw [card_triadicIndexBox (H + n), card_triadicIndexBox H, card_triadicIndexBox n,
      pow_add, mul_pow]
  have hcH_pos : (0 : ℝ) < ((triadicIndexBox d H).card : ℝ) := by
    rw [card_triadicIndexBox H]
    positivity
  have hcH_ne : ((triadicIndexBox d H).card : ℝ) ≠ 0 := ne_of_gt hcH_pos
  calc
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
        ∑ W ∈ triadicIndexBox d (H + n),
          (Real.sqrt (vecDot Y.1 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).lowerRight Y.2))) ^ 2 ∂P)
        = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            ∑ W ∈ triadicIndexBox d (H + n),
              ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      (b a)).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      (b a)).lowerRight Y.2))) ^ 2 ∂P := hLHS
    _ ≤ (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            ∑ W ∈ triadicIndexBox d (H + n),
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      b).lowerRight Y.2))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum_bound hcHn_inv_nonneg
    _ = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                        (fun i => 3 ^ n * w i + z i)) b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                        (fun i => 3 ^ n * w i + z i)) b).lowerRight Y.2))) ^ 2) := by
          rw [hreindex]
    _ = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).lowerRight Y.2))) ^ 2) := by
          rw [hdesc_sum]
    _ = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            (((triadicIndexBox d H).card : ℝ) *
              ∑ z ∈ triadicIndexBox d n,
                (Real.sqrt (vecDot Y.1 (matVecMul
                      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                        b).upperLeft Y.1))
                    + Real.sqrt (vecDot Y.2 (matVecMul
                      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                        b).lowerRight Y.2))) ^ 2) := by
          rw [hcollapse]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).lowerRight Y.2))) ^ 2 := by
          rw [hcard, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hcH_ne]

/-- **The annealed flat average of the squared pairing head at descendant depth `n`.**  Step ζ of
the cutoff-mean row of `p.response.transfer` at depth `n`, minus sign: the annealed flat average
over the generation-`(s-n)` cells of the terminal cell of the squared pathwise head is at most the
depth-`n` layer of the source load. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s) (Y : BlockVec d)
    (hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1)) P)
    (hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2)) P)
    (hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P)
    (hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P)
    (hUL0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1))
    (hLR0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2))
    (hcross : ∀ W : Fin d → ℤ, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffMinus F a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffMinus F a)).lowerRight Y.2))) P)
    (hsq : ∀ W : Fin d → ℤ, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffMinus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffMinus F a)).lowerRight Y.2))) ^ 2) P) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).lowerRight Y.2))) ^ 2 := by
  exact integral_avsum_sq_head_descendant_le_aux P jStar F (respCoeffMinus F) H n s Y
    hUL hLR hULe hLRe hUL0 hLR0 hcross hsq (fun w z =>
      annealedBlockOf_descendant_respCoeffMinus_eq P hstat jStar (explicitCanonicalMetric F) F s hjs
        n w z (hmeas z) (hmeas' z))

/-- **The annealed flat average of the squared pairing head at descendant depth `n`, plus
sign.**  The adjoint twin of `integral_avsum_sq_head_descendant_le_respCoeffMinus`, for the
recentred family `a_+ = a^t + g`. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s) (Y : BlockVec d)
    (hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1)) P)
    (hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2)) P)
    (hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P)
    (hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P)
    (hUL0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1))
    (hLR0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2))
    (hcross : ∀ W : Fin d → ℤ, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffPlus F a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffPlus F a)).lowerRight Y.2))) P)
    (hsq : ∀ W : Fin d → ℤ, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffPlus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffPlus F a)).lowerRight Y.2))) ^ 2) P) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).lowerRight Y.2))) ^ 2 := by
  exact integral_avsum_sq_head_descendant_le_aux P jStar F (respCoeffPlus F) H n s Y
    hUL hLR hULe hLRe hUL0 hLR0 hcross hsq (fun w z =>
      annealedBlockOf_descendant_respCoeffPlus_eq P hstat jStar (explicitCanonicalMetric F) F s hjs
        n w z (hmeas z) (hmeas' z))

end

end Homogenization.HighContrast.Multiscale
