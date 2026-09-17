import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSubcellCoeffOn
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# The response functional as a coarse-block quadratic form on an aligned subcell

The scalar response `ResponseJ U p r b` of AK.HC (2.9) is evaluated at the canonical
coarse-block quadratic expression `p·(A(-p, r))/2 - p·r` whenever `U` is an open bounded
convex domain carrying an elliptic representative of `b`, by
`responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain`
(`HCPoly/Entry/CG/Proofs/AdaptedDomainRecovery.lean`).  The recentred coefficients `a_- = a - g` and
`a_+ = aᵀ + g` carry such a representative on the parent adapted cell `⋄_t^q` and, via
`exists_elliptic_representative_respCoeffMinusAt` / `…PlusAt`, on every aligned triadic
subcell `adaptedCellAtCenter q k w`.

This module exposes that evaluation publicly, for the parent cell and for each aligned
subcell, so that the cell-average estimate of AK.HC (2.15) can be consumed downstream.  Nothing
new is proved here: each statement is the general bounded-convex-domain formula transported
along the a.e. equality of the elliptic representative.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The aligned subcell -/

/-- **AK.HC (2.15) on an aligned subcell, minus sign.**  For the recentred coefficient
`a_- = a - g`, the response functional on the aligned adapted subcell `adaptedCellAtCenter q k w`
equals the coarse-block quadratic expression `(-p, r)·(A_{kw}(-p, r))/2 - p·r`, where
`A_{kw}` is the coarse block matrix of `a_-` on that subcell. -/
theorem h6a_responseJ_adaptedCellAtCenter_respCoeffMinus (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (adaptedCellAtCenter q k w) p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffMinus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt q hq k w F a
  rw [Homogenization.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    Homogenization.coarseBlockMatrix_congr_of_ae_eq hae]
  exact Homogenization.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w) hEll
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) p r

/-- **AK.HC (2.15) on an aligned subcell, plus sign.**  The adjoint twin for the transposed
recentred coefficient `a_+ = aᵀ + g`. -/
theorem h6a_responseJ_adaptedCellAtCenter_respCoeffPlus (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (adaptedCellAtCenter q k w) p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffPlus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt q hq k w F a
  rw [Homogenization.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    Homogenization.coarseBlockMatrix_congr_of_ae_eq hae]
  exact Homogenization.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w) hEll
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) p r

/-! ## The parent adapted cell -/

/-- **AK.HC (2.15) on the parent adapted cell, minus sign.**  The public counterpart of the
parent-cell evaluation, for the recentred coefficient `a_- = a - g`. -/
theorem h6a_responseJ_adaptedCell_respCoeffMinus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (HighContrast.adaptedCell q t) p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  rw [Homogenization.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    Homogenization.coarseBlockMatrix_congr_of_ae_eq hae]
  exact Homogenization.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (adaptedCell_isOpenBoundedConvexDomain q hq t) hEll hvol p r

/-- **AK.HC (2.15) on the parent adapted cell, plus sign.**  The adjoint twin for the
transposed recentred coefficient `a_+ = aᵀ + g`. -/
theorem h6a_responseJ_adaptedCell_respCoeffPlus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (HighContrast.adaptedCell q t) p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  rw [Homogenization.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
    Homogenization.coarseBlockMatrix_congr_of_ae_eq hae]
  exact Homogenization.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (adaptedCell_isOpenBoundedConvexDomain q hq t) hEll hvol p r

end

end Homogenization.HighContrast.Multiscale
