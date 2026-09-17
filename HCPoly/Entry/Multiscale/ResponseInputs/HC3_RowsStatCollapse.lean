import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsStatBlock

/-!
# The flat average of the annealed heads collapses to the origin cell

In the cell half of the cutoff-mean row of `p.response.transfer` the terminal cell is
subdivided into the `3^{Hd}` cells of the coarse generation `s`, and each contributes the
square of the two-term head of its own annealed block.  Above `j_*` every aligned cell of a
given generation is an integer translate of the centred one and the law is translation
invariant, so all those annealed blocks coincide: the flat average over the triadic index
box collapses to the single head at the index `0`, the depth-zero summand of the source load
`respSourceLoad`.  This is the step that makes the scale-`s` subdivision cost nothing.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- **The flat average of the annealed heads collapses, minus sign.**  For a stationary law
`P` and the recentred coefficient `a_- = a - g` of `p.response.transfer`, at a scale
`j ≥ j_*` the normalized sum over the `3^{nd}` triadic subcells `adaptedCellAtCenter (respGrid jStar F) j w`
of the squared two-term head of the corresponding annealed block is the head of the single cell
at the index `0`.  Every subcell is an integer translate of the centred cell and the law is
translation invariant, so the summand is independent of `w`. -/
theorem avsum_sq_head_annealed_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (Y : BlockVec d)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffMinus F a)).lowerRight i k) P) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffMinus F)).lowerRight Y.2))) ^ 2 := by
  have h0mem : (0 : Fin d → ℤ) ∈ triadicIndexBox d n := by
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hcard : ((triadicIndexBox d n).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨0, h0mem⟩))
  simp only [respGrid]
  have hsum : ∀ w ∈ triadicIndexBox d n,
      (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j w)
            (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j w)
            (respCoeffMinus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j 0)
            (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j 0)
            (respCoeffMinus F)).lowerRight Y.2))) ^ 2 := by
    intro w _
    have hw := annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj w hmeas hmeas'
    have h0 := annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj 0 hmeas hmeas'
    simp only [hw.1, hw.2, h0.1, h0.2]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

/-- **The flat average of the annealed heads collapses, plus sign.**  For a stationary law
`P` and the recentred coefficient `a_+ = aᵀ + g` of `p.response.transfer`, at a scale
`j ≥ j_*` the normalized sum over the `3^{nd}` triadic subcells `adaptedCellAtCenter (respGrid jStar F) j w`
of the squared two-term head of the corresponding annealed block is the head of the single cell
at the index `0`.  Every subcell is an integer translate of the centred cell and the law is
translation invariant, so the summand is independent of `w`. -/
theorem avsum_sq_head_annealed_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (Y : BlockVec d)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffPlus F a)).lowerRight i k) P) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffPlus F)).lowerRight Y.2))) ^ 2 := by
  have h0mem : (0 : Fin d → ℤ) ∈ triadicIndexBox d n := by
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hcard : ((triadicIndexBox d n).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨0, h0mem⟩))
  simp only [respGrid]
  have hsum : ∀ w ∈ triadicIndexBox d n,
      (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j w)
            (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j w)
            (respCoeffPlus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j 0)
            (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j 0)
            (respCoeffPlus F)).lowerRight Y.2))) ^ 2 := by
    intro w _
    have hw := annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj w hmeas hmeas'
    have h0 := annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj 0 hmeas hmeas'
    simp only [hw.1, hw.2, h0.1, h0.2]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

end

end Homogenization.HighContrast.Multiscale
