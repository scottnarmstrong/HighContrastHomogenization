import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCellHyp

/-!
# The recent-difference energy map on an aligned cell

This composes the recent-difference energy map on the doubled response space with the per-cell
bookkeeping of the weak-norm estimate.  The response-size input is taken at the square of the
printed geometric factor, and the metric factor is the operator norm of the normalized reference
block, which on positive definite carriers is the printed spectral bound.

The remaining input is the identification of the Chapter-2 coarse block with the shear
congruence of the cell's coarse block.  The two coarse-block carriers used here — the Chapter-2
`coarseBlockMatrix` on a `Domain` and the set-level `coarseBlockMatrix` on the cell — are not
identified by any declaration in this module's import closure, so that identification is carried
as an explicit hypothesis.
-/

open Homogenization.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The recent-difference energy map on an aligned cell, with the response-size factor supplied
through the shear congruence.  For every index `w` in the triadic box, the metric square of the
cell average of the doubled difference of two optimizers is bounded by the printed geometric
square times the actual difference energy on that cell.

The hypothesis `hcoarse` identifies the Chapter-2 coarse block of the recentred coefficient with
the shear congruence of the cell's coarse block; it is the shape the shear identity produces and
the one input this module cannot discharge from its own imports. -/
theorem h6a_recentEnergyMap_port
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (a : CoeffSpace d) (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    (u v : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hEll : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hcoarse : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) =
        blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a))
    (hG : ∀ w ∈ triadicIndexBox d n, 0 ≤ Book.Ch02.average
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
      (fun x => blockVecDot
        (optimizerField (aU w).toCoeffField (u w) x -
          optimizerField (aU w).toCoeffField (v w) x)
        (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
          (optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x)))) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => optimizerField (aU w).toCoeffField (u w) x -
              optimizerField (aU w).toCoeffField (v w) x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => optimizerField (aU w).toCoeffField (u w) x -
              optimizerField (aU w).toCoeffField (v w) x)))
      ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2
        * Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
            (fun x => blockVecDot
              (optimizerField (aU w).toCoeffField (u w) x -
                optimizerField (aU w).toCoeffField (v w) x)
              (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
                (optimizerField (aU w).toCoeffField (u w) x -
                  optimizerField (aU w).toCoeffField (v w) x))) := by
  have hNpd : (toFullBlockMat
      (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))).PosDef :=
    Annealed.normalizedBlock_posDef _ _ hEhat hM0
  have hnorm_pos : 0 < ‖toFullBlockMat
      (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ :=
    norm_pos_iff.mpr hNpd.isUnit.ne_zero
  have hBpos : 0 < 1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
      * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hsize : ‖toFullBlockMat
        (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2
      ≤ (Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 := by
    rw [h6a_blockSpecBound_eq_norm_of_posSemidef _ hNpd.posSemidef, mul_pow,
      Real.sq_sqrt (norm_nonneg _)]
  refine h6a_hcell_of_metric_and_size (P := P) (γ := γ) (jStar := jStar) (F := F) (t := t)
    (a := a) (n := n)
    (Y := fun w x => optimizerField (aU w).toCoeffField (u w) x -
      optimizerField (aU w).toCoeffField (v w) x)
    (G := fun w => Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
      (fun x => blockVecDot
        (optimizerField (aU w).toCoeffField (u w) x -
          optimizerField (aU w).toCoeffField (v w) x)
        (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x)
          (optimizerField (aU w).toCoeffField (u w) x -
            optimizerField (aU w).toCoeffField (v w) x))))
    (k := ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖)
    (e := (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
        * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2)
    (hk := hnorm_pos.le) (he := (pow_pos hBpos 2).le) (hG := hG) (hsize := hsize) (hmetric := ?_)
  intro w hw
  have hAE : toFullBlockMat
        (Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w))
      ≤ (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
          * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2
        • toFullBlockMat (respEhatMinus P jStar F t) := by
    rw [hcoarse w hw]
    exact h6a_coarseBlock_congr_le_sq_smul_respEhatMinus P γ jStar F t a n hw hbdd hEmean
  have hEM : toFullBlockMat (respEhatMinus P jStar F t)
      ≤ ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖
        • toFullBlockMat (respM0 F) :=
    h6a_le_smul_of_normalizedBlock hEhat.posSemidef hM0
  have hmain := h6a_recent_difference_metric_le
    (U := adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (a := aU w)
    (hEll w) (u w) (v w) hm hEhat hnorm_pos (pow_pos hBpos 2) hEM hAE
  simpa only using! hmain

end

end Homogenization.HighContrast.Multiscale
