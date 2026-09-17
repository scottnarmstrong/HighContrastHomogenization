import HCPoly.Entry.CG.Proofs.AdaptedDomainRecovery
import HCPoly.Entry.Setup.BlockCalculus

/-!
# Positive semidefiniteness of the coarse block of a cell

On a bounded open convex domain carrying a pointwise elliptic coefficient field, the canonical
coarse block matrix is the Hessian of the minimal block energy `Mu` with prescribed doubled mean.
That energy is an infimum of averages of a nonnegative density, hence nonnegative, so the block is
positive semidefinite. In particular its two diagonal blocks — the `b` and the `S_*^{-1}` appearing
in `e.response.cutoff.estimate` — are positive semidefinite, which are the side conditions of the
direct full-dual pairing.
-/

open Homogenization.HighContrast.CG

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The coarse block of a cell is positive semidefinite: for every doubled vector `X` the
quadratic form `X · (blockMatVecMul (coarseBlockMatrix V b) X)` is nonnegative. -/
theorem zero_le_blockVecDot_coarseBlockMatrix {d : ℕ} [NeZero d] {V : Set (Vec d)}
    {lam Lam : ℝ} {b : CoeffField d} (hConv : IsOpenBoundedConvexDomain V)
    (hEll : IsEllipticFieldOn lam Lam V b) (hvol : 0 < (volume V).toReal) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul (coarseBlockMatrix V b) X) := by
  have hMu_nonneg : 0 ≤ Mu V X b := by
    refine le_Mu_of_forall_isBlockMuAdmissible fun Y _ => ?_
    unfold volumeAverage
    refine mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hConv.isOpen.measurableSet] with x hx
    have hco := blockMatrixOfCoeff_coercive_of_isEllipticMatrix (hEll.2 x hx) (Y.eval x)
    have hZ : 0 ≤ blockVecDot (Y.eval x) (Y.eval x) := blockVecDot_nonneg (Y.eval x)
    have hc : 0 ≤ lam / (1 + 2 * Lam ^ 2) :=
      div_nonneg (hEll.2 x hx).1.le (by positivity)
    have hmain : 0 ≤ blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (b x)) (Y.eval x)) :=
      le_trans (mul_nonneg hc hZ) hco
    unfold blockEnergyDensity blockCoeffField
    exact mul_nonneg (by norm_num) hmain
  have hMu_eq : Mu V X b =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (coarseBlockMatrix V b) X) :=
    (isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hConv hEll hvol).2 X
  rw [hMu_eq] at hMu_nonneg
  linarith

/-- The upper-left diagonal block of the coarse block matrix is positive semidefinite: the block
quadratic form of `(p, 0)` is `p · (upperLeft p)`. -/
theorem zero_le_vecDot_coarseBlockMatrix_upperLeft {d : ℕ} [NeZero d] {V : Set (Vec d)}
    {lam Lam : ℝ} {b : CoeffField d} (hConv : IsOpenBoundedConvexDomain V)
    (hEll : IsEllipticFieldOn lam Lam V b) (hvol : 0 < (volume V).toReal) (p : Vec d) :
    0 ≤ vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p) := by
  have h := zero_le_blockVecDot_coarseBlockMatrix hConv hEll hvol (p, 0)
  have hquad : blockVecDot (p, 0) (blockMatVecMul (coarseBlockMatrix V b) (p, 0))
      = vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p) := by
    simp [blockVecDot, matVecMul_zero, vecDot_zero_left]
  rwa [hquad] at h

/-- The lower-right diagonal block of the coarse block matrix is positive semidefinite: the block
quadratic form of `(0, r)` is `r · (lowerRight r)`. -/
theorem zero_le_vecDot_coarseBlockMatrix_lowerRight {d : ℕ} [NeZero d] {V : Set (Vec d)}
    {lam Lam : ℝ} {b : CoeffField d} (hConv : IsOpenBoundedConvexDomain V)
    (hEll : IsEllipticFieldOn lam Lam V b) (hvol : 0 < (volume V).toReal) (r : Vec d) :
    0 ≤ vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r) := by
  have h := zero_le_blockVecDot_coarseBlockMatrix hConv hEll hvol (0, r)
  have hquad : blockVecDot (0, r) (blockMatVecMul (coarseBlockMatrix V b) (0, r))
      = vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r) := by
    simp [blockVecDot, matVecMul_zero, vecDot_zero_left]
  rwa [hquad] at h

end

end Homogenization.HighContrast.Multiscale
