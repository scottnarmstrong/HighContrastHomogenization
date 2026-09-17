import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentAssemblyPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadCellPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadEnergyCarrierPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakChildIntegrable
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakMeanPosDef
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakEhatPosDef
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakPrimalDegenerate

/-!
# The finite-window head of the cell-average estimate at the carriers, adjoint sign

The recent head of `l.weaknorms.moreproto` is bounded by the two finite defect sums once two
analytic facts are supplied at each depth: a per-cell metric bound for the recent difference of
the parent optimizer and a child optimizer, and an averaged bound for the difference energies.
Both are now available at the estimate's own grid, sample, metric and maximizer, so the head
carries no analytic hypothesis of its own: the coefficient's positive definiteness comes from the
law-integrability of the coarse block on the cell, and every geometric input from invertibility of
the selected grid.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The finite-window head of the cell-average estimate, at the carriers.**  On the branch
where the all-scale maximum does not exceed `1`, the `3^{-n/2}`-weighted sum over the window
`n ≤ H` of the normalized `L²` averages of the recentred transported subcell averages is bounded
by `16 K L` times the sum of the two finite defect sums, where `K` is the square root of the
printed spectral bound of the normalized reference block and `L` the square root of the response
load. -/
theorem h6a_recentHead_carrier_plus (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1) :
    ∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a) u) -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a) u) -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u))))
      ≤ 16 *
          Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqPlus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
              (respCoeffPlus F a) +
            weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
              (respCoeffPlus F a)) := by
  classical
  have hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
    h6a_respEhatPlus_posDef_of_integrable hgrid t hint
  have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
    h6a_respM0_posDef_of_isUnit_respGrid hgrid
  have hm : (explicitCanonicalMetric F).PosDef :=
    h6a_explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid
  have hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    h6a_respMean_posDef_of_integrable hgrid t hint
  have h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun n _ w hw j =>
    (h6a_integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hgrid t F a u n w
      hw j).1
  have h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun n _ w hw j =>
    (h6a_integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hgrid t F a u n w
      hw j).2
  obtain ⟨V, hV⟩ :=
    h6a_recentHead_actual_of_analytic_plus P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood h1u h2u
  refine hV (fun n _ w _ j =>
      (h6a_integrableOn_optimizerField_respCoeffPlus_at (respGrid jStar F) hgrid
        (t - (n : ℤ)) w F a ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) j).1)
    (fun n _ w _ j =>
      (h6a_integrableOn_optimizerField_respCoeffPlus_at (respGrid jStar F) hgrid
        (t - (n : ℤ)) w F a ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) j).2)
    (fun n => ?_)
  refine ⟨fun w => 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
    (fun x => vecDot
      (optimizerField (respCoeffPlus F a) u x -
        optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1
      (optimizerField (respCoeffPlus F a) u x -
        optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2), ?_, ?_⟩
  · exact h6a_headCell_of_bridge_plus P γ jStar F t hgrid a n u
      (fun w => (V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) hm hEmean hE hM0 hbdd
  · exact h6a_headEnergy_carrier_plus P jStar F t e hgrid a n u hu
      (fun w => (V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)
      (fun w _ => (V n w).isMaximizer) hE

end

end Homogenization.HighContrast.Multiscale
