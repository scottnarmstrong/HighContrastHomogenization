import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsHeadExpect
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsBlockIntegral

/-!
# The annealed head of one descendant generation

The source load `L_s` of `p.response.transfer` is the sum over the descendant generations of
`3^{-3n/2}` times the flat average over that generation's cells of `(√α + √β)^2`, where `α` and `β`
are the two diagonal quadratic forms of the **annealed** coarse block of the cell.  The pairing of
the cutoff row produces instead the flat average of the same expression built from the **pathwise**
coarse blocks, followed by the expectation.  Moving the expectation inside a single generation is
the content here: for each cell the expectation of `(√α + √β)^2` is at most `(√E[α] + √E[β])^2`
by the sample Cauchy--Schwarz inequality, and the expectation of each pathwise coarse-block
quadratic form is the quadratic form of the annealed block.  Averaging over the cells of the
generation therefore recovers that generation's own summand of `L_s`, with the expectation on the
inside and no inversion and no Jensen step in the wrong direction.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The annealed head of one descendant generation.**  The flat cell average over the generation
of `3^{-3n/2}` subcells of `(√α + √β)^2` integrates to at most the corresponding flat average of
`(√E[α] + √E[β])^2`, where `α` and `β` are the upper-left and lower-right pathwise coarse-block
quadratic forms and the square roots on the right are taken of their annealed counterparts.  This is
the step that moves the expectation inside one generation's summand of the source load `L_s` of
`p.response.transfer`. -/
theorem integral_avsum_pathwise_head_le {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (k : ℤ) (n : ℕ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hUL : ∀ w ∈ triadicIndexBox d n, ∀ a : CoeffSpace d, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
    (hLR : ∀ w ∈ triadicIndexBox d n, ∀ a : CoeffSpace d, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2))
    (hentUL : ∀ w ∈ triadicIndexBox d n, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d n, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d n, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d n, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d n, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d n, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
        ^ 2) P) :
    (∫ a, ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
          ^ 2 ∂P)
      ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).lowerRight Y.2)))
            ^ 2 := by
  have hc0 : 0 ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hstep : ∀ w ∈ triadicIndexBox d n,
      (∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
          ^ 2 ∂P)
        ≤ (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).lowerRight Y.2)))
          ^ 2 := by
    intro w hw
    have hul := integral_vecDot_coarseBlock_upperLeft (P := P)
      (V := adaptedCellAtCenter (respGrid jStar F) k w) b Y.1 (hentUL w hw)
    have hlr := integral_vecDot_coarseBlock_lowerRight (P := P)
      (V := adaptedCellAtCenter (respGrid jStar F) k w) b Y.2 (hentLR w hw)
    have h := integral_sq_sqrt_add_sqrt_le P (hqUL w hw) (hqLR w hw) (hUL w hw)
      (hLR w hw) (hcross w hw) (hsq w hw)
    simp only [hul, hlr] at h
    exact h
  calc
    (∫ a, ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
          ^ 2 ∂P)
      = ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∫ a, ∑ w ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
              ^ 2 ∂P := integral_const_mul _ _
    _ = ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
              ^ 2 ∂P := by
        rw [integral_finsetSum _ (fun w hw => hsq w hw)]
    _ ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).lowerRight Y.2)))
              ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hc0

end

end Homogenization.HighContrast.Multiscale
