import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCellRow
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsHeadDepth
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsStatCollapse
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsHead0

/-!
# The cell half of the cutoff-mean row on the carriers

The cell half of the two cutoff-mean rows of `e.response.cutoff.estimate` is the flat average,
over the `3^{Hd}` coarse cells of the terminal cell, of the cell mean of the cutoff times the
crossed dual pairing of that cell's optimizer-mean defect.  AK's direct full-dual pairing bounds
each cell's pairing pathwise by the cell's own two-term head times the square root of twice the
cell deficit; Cauchy--Schwarz with the expectation outside the flat average separates the two
factors, the expectation meets the pathwise coarse blocks linearly through
`integral_avsum_pathwise_head_le`, stationarity collapses the flat average of the annealed blocks
to the single cell at the origin through `avsum_sq_head_annealed_respCoeffMinus_eq`, and
`sq_head_le_respSourceLoad` identifies that collapsed head with the depth-zero summand of the
source load `L_s` of `p.response.transfer`.  The second factor is the annealed flat average of the
cell deficits, which is twice the scale defect `tau`.  This module assembles those landed pieces
into the two carrier-level estimates, one for each sign of the recentred coefficient.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- **The cell half of the cutoff-mean row, minus sign.**  On the carriers of
`p.response.transfer`, let `pairing` be the full-dual pairing of the optimizer-mean defect and let
`D` be the scalar cell deficit.  If each cell's pairing is controlled pathwise by the cell's own
two-term head
`√(P · b_s^{1/2} P) + √(Q · (S_{*,s})^{-1/2} Q)` of the pathwise coarse block of the recentred
coefficient `a_- = a - g` times `√(2 D)`, and the annealed flat average of `2 D` is `2 tau^-`,
then, provided the pathwise coarse blocks are nonnegative, integrable and measurable as
prescribed, the modulus of the sample expectation of the cutoff-weighted flat average of the
pairing is at most `√(L_s^-) * √(2 tau^-)`, where `L_s^-` is the source load of
`p.response.transfer` at the recentred coefficient `a_-` and the dual variable `Y^-`.  This is the
cell half of the cutoff-mean row, with the expectation outside the flat average and no inversion
of an annealed block and no Jensen step. -/
theorem abs_integral_avsum_weighted_pairing_le_respLsMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (hjs : (jStar : ℤ) ≤ s)
    (c : (Fin d → ℤ) → ℝ) (hc : ∀ w ∈ triadicIndexBox d H, |c w| ≤ 1)
    (pairing D : (Fin d → ℤ) → CoeffSpace d → ℝ)
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F)
      (respYMinus P jStar F t e)))
    (hD : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤ D w a)
    (hbd : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |pairing w a|
        ≤ (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2)))
          * Real.sqrt (2 * D w a))
    (hDval : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a ∂P) = 2 * respTauMinus P jStar F s t e)
    (hUL : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1))
    (hLR : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2))
    (hentUL : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        * Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
          + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2))) ^ 2) P)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffMinus F a)).lowerRight i k) P)
    (hFint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                (respYMinus P jStar F t e).2))) ^ 2) P)
    (hDint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                  (respYMinus P jStar F t e).1))
              + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                  (respYMinus P jStar F t e).2))) ^ 2)
        * Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, 2 * D w a)) P)
    (hPint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w *
        (Real.sqrt ((Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                    (respYMinus P jStar F t e).1))
                + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                    (respYMinus P jStar F t e).2))) ^ 2) * Real.sqrt (2 * D w a))) P)
    (hPint' : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w * pairing w a) P) :
    |∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * pairing w a ∂P|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e) := by
  have hG : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))) := by
    intro w hw a
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hGsq : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
          + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2))) ^ 2 ∂P)
      ≤ respLsMinus P jStar F s t e := by
    calc
      (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                  (respYMinus P jStar F t e).1))
              + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                  (respYMinus P jStar F t e).2))) ^ 2 ∂P)
          ≤ ((triadicIndexBox d H).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d H,
                (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F)).upperLeft
                      (respYMinus P jStar F t e).1))
                  + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F)).lowerRight
                      (respYMinus P jStar F t e).2))) ^ 2 :=
            integral_avsum_pathwise_head_le (P := P) (jStar := jStar) (F := F)
              (k := s) (n := H) (b := respCoeffMinus F) (Y := respYMinus P jStar F t e)
              hUL hLR hentUL hentLR hqUL hqLR hcross hsq
      _ = (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffMinus F)).upperLeft
                (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffMinus F)).lowerRight
                (respYMinus P jStar F t e).2))) ^ 2 :=
            avsum_sq_head_annealed_respCoeffMinus_eq (P := P) (hstat := hstat)
              (jStar := jStar) (F := F) (j := s) (hj := hjs) (n := H)
              (Y := respYMinus P jStar F t e) hmeas hmeas'
      _ ≤ respLsMinus P jStar F s t e := by
            simpa only [respLsMinus] using
              sq_head_le_respSourceLoad (P := P) (jStar := jStar) (F := F) (s := s)
                (b := respCoeffMinus F) (Y := respYMinus P jStar F t e) hsum
  exact abs_integral_flat_weighted_pairing_le (P := P) (Z := triadicIndexBox d H)
    (c := c) (hc := hc) (pairing := pairing)
    (G := fun w a =>
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))))
    (D := D) (Lhead := respLsMinus P jStar F s t e)
    (tau := respTauMinus P jStar F s t e)
    hG hD hbd hGsq hDval hFint hDint hMidint hPint hPint'

/-- **The cell half of the cutoff-mean row, plus sign.**  This is the `Plus` twin of
`abs_integral_avsum_weighted_pairing_le_respLsMinus`: the same flat-average estimate with the
recentred coefficient `a_+ = aᵀ + g`, the dual variable `Y^+`, the annealed head collapse
`avsum_sq_head_annealed_respCoeffPlus_eq`, the scale defect `tau^+` and the source load `L_s^+` of
`p.response.transfer`. -/
theorem abs_integral_avsum_weighted_pairing_le_respLsPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (hjs : (jStar : ℤ) ≤ s)
    (c : (Fin d → ℤ) → ℝ) (hc : ∀ w ∈ triadicIndexBox d H, |c w| ≤ 1)
    (pairing D : (Fin d → ℤ) → CoeffSpace d → ℝ)
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F)
      (respYPlus P jStar F t e)))
    (hD : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤ D w a)
    (hbd : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |pairing w a|
        ≤ (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2)))
          * Real.sqrt (2 * D w a))
    (hDval : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a ∂P) = 2 * respTauPlus P jStar F s t e)
    (hUL : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1))
    (hLR : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2))
    (hentUL : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        * Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
          + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2))) ^ 2) P)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffPlus F a)).lowerRight i k) P)
    (hFint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                (respYPlus P jStar F t e).2))) ^ 2) P)
    (hDint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                  (respYPlus P jStar F t e).1))
              + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                  (respYPlus P jStar F t e).2))) ^ 2)
        * Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, 2 * D w a)) P)
    (hPint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w *
        (Real.sqrt ((Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                    (respYPlus P jStar F t e).1))
                + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                    (respYPlus P jStar F t e).2))) ^ 2) * Real.sqrt (2 * D w a))) P)
    (hPint' : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w * pairing w a) P) :
    |∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * pairing w a ∂P|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e) := by
  have hG : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))) := by
    intro w hw a
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hGsq : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
          + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2))) ^ 2 ∂P)
      ≤ respLsPlus P jStar F s t e := by
    calc
      (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                  (respYPlus P jStar F t e).1))
              + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                  (respYPlus P jStar F t e).2))) ^ 2 ∂P)
          ≤ ((triadicIndexBox d H).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d H,
                (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F)).upperLeft
                      (respYPlus P jStar F t e).1))
                  + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F)).lowerRight
                      (respYPlus P jStar F t e).2))) ^ 2 :=
            integral_avsum_pathwise_head_le (P := P) (jStar := jStar) (F := F)
              (k := s) (n := H) (b := respCoeffPlus F) (Y := respYPlus P jStar F t e)
              hUL hLR hentUL hentLR hqUL hqLR hcross hsq
      _ = (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffPlus F)).upperLeft
                (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffPlus F)).lowerRight
                (respYPlus P jStar F t e).2))) ^ 2 :=
            avsum_sq_head_annealed_respCoeffPlus_eq (P := P) (hstat := hstat)
              (jStar := jStar) (F := F) (j := s) (hj := hjs) (n := H)
              (Y := respYPlus P jStar F t e) hmeas hmeas'
      _ ≤ respLsPlus P jStar F s t e := by
            simpa only [respLsPlus] using
              sq_head_le_respSourceLoad (P := P) (jStar := jStar) (F := F) (s := s)
                (b := respCoeffPlus F) (Y := respYPlus P jStar F t e) hsum
  exact abs_integral_flat_weighted_pairing_le (P := P) (Z := triadicIndexBox d H)
    (c := c) (hc := hc) (pairing := pairing)
    (G := fun w a =>
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))))
    (D := D) (Lhead := respLsPlus P jStar F s t e)
    (tau := respTauPlus P jStar F s t e)
    hG hD hbd hGsq hDval hFint hDint hMidint hPint hPint'

end

end Homogenization.HighContrast.Multiscale
