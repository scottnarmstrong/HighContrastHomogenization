import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsBlockPSD
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSubcellCoeffOn

/-!
# Nonnegativity of the two diagonal coarse-block forms of the recentred families

The source-load head of `p.response.transfer` is the sum of the square roots of the two diagonal
coarse-block quadratic forms of the recentred coefficient on an aligned cell.  Both forms are
nonnegative because the coarse block of an elliptic coefficient is positive semidefinite.  The
recentred coefficients `a_∓ = respCoeff∓ F a` are elliptic only almost everywhere, so each
statement is proved at a pointwise elliptic representative on the aligned cell and transported
back, the coarse block being unchanged by an almost-everywhere replacement of the coefficient.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The two diagonal coarse-block forms of `a_- = a - g` are nonnegative on every aligned
cell.**  Both entries of the source-load head of `p.response.transfer` are well defined on every
aligned cell of the response grid. -/
theorem zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (k : ℤ) (a : CoeffSpace d) (Y : BlockVec d)
    (W : Fin d → ℤ) :
    0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffMinus F a)).upperLeft Y.1)
      ∧ 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffMinus F a)).lowerRight Y.2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt (respGrid jStar F) hq k W F a
  have hC : coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) f =
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffMinus F a) :=
    (Homogenization.coarseBlockMatrix_congr_of_ae_eq hae).symm
  constructor
  · have h := zero_le_vecDot_coarseBlockMatrix_upperLeft
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.1
    simpa only [hC] using h
  · have h := zero_le_vecDot_coarseBlockMatrix_lowerRight
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.2
    simpa only [hC] using h

/-- **The two diagonal coarse-block forms of `a_+ = aᵀ + g` are nonnegative on every aligned
cell.**  The adjoint twin of
`zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter`. -/
theorem zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (k : ℤ) (a : CoeffSpace d) (Y : BlockVec d)
    (W : Fin d → ℤ) :
    0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffPlus F a)).upperLeft Y.1)
      ∧ 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W)
            (respCoeffPlus F a)).lowerRight Y.2) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt (respGrid jStar F) hq k W F a
  have hC : coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) f =
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffPlus F a) :=
    (Homogenization.coarseBlockMatrix_congr_of_ae_eq hae).symm
  constructor
  · have h := zero_le_vecDot_coarseBlockMatrix_upperLeft
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.1
    simpa only [hC] using h
  · have h := zero_le_vecDot_coarseBlockMatrix_lowerRight
      (isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq k W) hEll
      (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq k W) Y.2
    simpa only [hC] using h

end

end Homogenization.HighContrast.Multiscale
