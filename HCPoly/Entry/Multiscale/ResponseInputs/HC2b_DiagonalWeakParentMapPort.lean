import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentEnergyMapPort

/-!
# The parent-optimizer energy map on an aligned cell

This is the per-cell bookkeeping of the weak-norm estimate for the single parent optimizer field
instead of a difference.  The metric square of the cell average of the parent state is bounded by
the square of the printed geometric factor times the Chapter-2 block energy of the aligned
subcell, the energy carried by the restricted solution whose gradient agrees with the parent's.

The proof is the recent-difference bookkeeping with the recent-difference metric input replaced by
the cell energy bound for the parent optimizer on an aligned subcell.
-/

open Homogenization.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The parent-optimizer energy map on an aligned cell.  For every index `w` in the triadic box,
the metric square of the cell average of the parent optimizer field on the aligned subcell is
bounded by the printed geometric square times twice the Chapter-2 block energy of the restricted
solution there; that energy is the actual state energy on the subcell, not a difference energy.

The hypothesis `hcoarse` identifies the Chapter-2 coarse block of the recentred coefficient with
the shear congruence of the subcell's coarse block, exactly as in the recent-difference map. -/
theorem h6a_parentEnergyMap_port
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (a : CoeffSpace d) (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    {V : Set (Vec d)}
    (u : (w : Fin d → ℤ) → AHarmonicFunction (aU w).toCoeffField V)
    (z : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hz : ∀ w, (z w).toH1.grad = (u w).toH1.grad)
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
        blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
      ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2
        * (2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (aU w).toCoeffField (z w) ^ 2) := by
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
    (Y := fun w x => optimizerField (aU w).toCoeffField (u w) x)
    (G := fun w => 2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (aU w).toCoeffField (z w) ^ 2)
    (k := ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖)
    (e := (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
        * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2)
    (hk := hnorm_pos.le) (he := (pow_pos hBpos 2).le) (hG := fun _ _ => by positivity)
    (hsize := hsize) (hmetric := ?_)
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
  have hmain := h6a_blockSq_cellAverage_optimizerField_adaptedCellAtCenter_le
    (q := respGrid jStar F) (hq := hgrid) (k := t - (n : ℤ)) (w := w)
    (E := respEhatMinus P jStar F t)
    (aU w) (hEll w) (u w) (z w) (hz w) hm hEhat hnorm_pos (pow_pos hBpos 2) hEM hAE
  simpa only using hmain

end

end Homogenization.HighContrast.Multiscale
