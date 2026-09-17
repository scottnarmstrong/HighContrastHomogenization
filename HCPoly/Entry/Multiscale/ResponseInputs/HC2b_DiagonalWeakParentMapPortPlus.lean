import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakParentMapPort
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakEnergyMapPlus

/-!
# The parent-optimizer energy map, adjoint sign

The parent-optimizer energy map of `HC2b_DiagonalWeakParentMapPort` is stated for the recentred
sample `respEhatMinus`.  The adjoint copy is needed for the `a_+` per-scale input, whose sample is
`respEhatPlus = blockAdjoint (respEhatMinus …)`.  Because the adjoint adds one congruence by the
flux flip `D`, the response-size input is no longer a bound for the shear factor `respG F` alone:
it is the composed factor `D ∘ respG F`.

As in the recent-difference adjoint twin, the map is split so that the large block terms are
elaborated once each: the per-cell step carries the two Loewner constants abstract and is the
aligned-subcell instance of the Chapter-2 block energy bound for the parent optimizer, and the
second theorem feeds it the adjoint size inputs.  The remaining input of the second theorem is the
identification of the Chapter-2 coarse block of the recentred adjoint field with the composed
congruence of the cell's coarse block; the two coarse-block carriers used here — the Chapter-2
`coarseBlockMatrix` on a `Domain` and the set-level `coarseBlock` on the cell — are not identified
by any declaration in this module's import closure, so that identification is carried as an
explicit hypothesis, exactly as for the minus sign.
-/

open Homogenization.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The per-cell step of the parent-optimizer energy map for the adjoint sample, with the two
Loewner constants abstract.  This is the aligned-subcell Chapter-2 block energy bound for the
parent optimizer `u`, whose gradient agrees with the restricted solution `z`: the metric square of
the cell average of the parent state is bounded by the product `k * e` of the two Loewner sizes
times twice the actual state energy carried by `z`.  The reference sample is `respEhatPlus`, the
root is `blockSqrt (respM0 F)`, and the response sample and the two Loewner hypotheses are those of
the weak-norm estimate (`e.response.weak.estimate`). -/
theorem h6a_parentEnergyMap_cell_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (n : ℕ)
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
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (k e : ℝ) (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat (respEhatPlus P jStar F t) ≤ k • toFullBlockMat (respM0 F))
    (hAE : ∀ w ∈ triadicIndexBox d n,
      toFullBlockMat (Book.Ch02.coarseBlockMatrix
          (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
        ≤ e • toFullBlockMat (respEhatPlus P jStar F t)) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
      ≤ (k * e) * (2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (aU w).toCoeffField (z w) ^ 2) := by
  intro w hw
  simpa only using h6a_blockSq_cellAverage_optimizerField_adaptedCellAtCenter_le
    (q := respGrid jStar F) (hq := hgrid) (k := t - (n : ℤ)) (w := w)
    (E := respEhatPlus P jStar F t)
    (aU w) (hEll w) (u w) (z w) (hz w) hm hEhat hk he hEM (hAE w hw)

/-- The parent-optimizer energy map on an aligned cell for the adjoint sample.  This is the adjoint
twin of `h6a_parentEnergyMap_port` (`HC2b_DiagonalWeakParentMapPort.lean`): the sample is
`respEhatPlus`, and the response-size input `hcoarse` identifies the Chapter-2 coarse block of the
recentred field with the composed congruence `D ∘ respG F`, the factor the adjoint carries.  The
per-cell step is `h6a_parentEnergyMap_cell_plus` above. -/
theorem h6a_parentEnergyMap_port_plus
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
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hcoarse : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) =
        blockCongr (blockD d)
          (blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a))) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
      ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2
        * (2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (aU w).toCoeffField (z w) ^ 2) := by
  have hNpd : (toFullBlockMat
      (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))).PosDef :=
    Annealed.normalizedBlock_posDef _ _ hEhat hM0
  have hnorm_pos : 0 < ‖toFullBlockMat
      (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ :=
    norm_pos_iff.mpr hNpd.isUnit.ne_zero
  have hBpos : 0 < 1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
      * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hsize : ‖toFullBlockMat
        (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2
      ≤ (Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 := by
    rw [h6a_blockSpecBound_eq_norm_of_posSemidef _ hNpd.posSemidef, mul_pow,
      Real.sq_sqrt (norm_nonneg _)]
  refine h6a_hcell_of_constants (triadicIndexBox d n)
    (fun w => blockVecDot
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField (aU w).toCoeffField (u w))))
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField (aU w).toCoeffField (u w)))))
    (fun w => 2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (aU w).toCoeffField (z w) ^ 2)
    (‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
      * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
          * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2)
    ((Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2)
    (mul_nonneg hnorm_pos.le (pow_pos hBpos 2).le) (fun _ _ => by positivity) hsize ?_
  exact h6a_parentEnergyMap_cell_plus P jStar F t hgrid n aU u z hz hEll hm hEhat
    ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
    ((1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
        * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2)
    hnorm_pos (pow_pos hBpos 2)
    (h6a_le_smul_of_normalizedBlock hEhat.posSemidef hM0)
    (fun w hw => by
      rw [hcoarse w hw]
      exact h6a_blockCongr_le_smul (blockD d)
        (h6a_coarseBlock_congr_le_sq_smul_respEhatMinus P γ jStar F t a n hw hbdd hEmean))

end

end Homogenization.HighContrast.Multiscale
