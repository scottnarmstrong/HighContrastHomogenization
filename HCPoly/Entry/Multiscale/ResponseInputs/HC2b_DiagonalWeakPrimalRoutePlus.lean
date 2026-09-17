import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadBranchfree
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakTailRoutePlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadRoutePlus

/-!
# The cell-average estimate for the transposed recentred coefficient

The adjoint twin of the cell-average estimate `l.weaknorms.moreproto`: the two older-scale
branches at the estimate's own carriers and the finite-window head compose through the branch-free
selector, exactly as for the recentred coefficient itself.  The statement is the route's, carried
here so that the route file stays short.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The cell-average estimate, adjoint sign.**  The scale-average seminorm of the recentred
doubled optimizer state of the transposed recentred coefficient is bounded by the two finite
recent-scale sums plus the older-scale energy term, with the printed cutoff selector.  See
`e.response.weak.estimate`. -/
theorem h6a_diagonalWeakNorm_primal_plus (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        besovSeminorm t (fun n w =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))) ≤
      16 * Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqPlus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) +
            weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
              (respCoeffPlus F a)) +
        (16 / (1 - respRho γ) *
            Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))) *
          (if 1 < respAllScaleMax P γ jStar F t a then
              Real.sqrt (respAllScaleMax P γ jStar F t a)
            else (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u := by
  classical
  have hrho : respRho γ < 1 := by
    have := _hγ.2
    rw [respRho]
    linarith only [this]
  have hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
    h6a_respEhatPlus_posDef_of_integrable hgrid t hint
  have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
    h6a_respM0_posDef_of_isUnit_respGrid hgrid
  have hm : (explicitCanonicalMetric F).PosDef :=
    h6a_explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid
  have hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    h6a_respMean_posDef_of_integrable hgrid t hint
  obtain ⟨hbad, hgood⟩ :=
    h6a_tailBranches_plus P γ _hγ jStar H F t hgrid a u hm hEmean hE hM0 hbdd
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) with hKdef
  set L : ℝ := Real.sqrt (respLsqPlus P jStar F t e) with hLdef
  set Ene : ℝ := weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u with hEnedef
  set Sums : ℝ := 16 * K * L *
    (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) +
      weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatPlus P jStar F t)
        (respCoeffPlus F a)) with hSumsdef
  set c : ℝ := 16 / (1 - respRho γ) * K with hcdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hEne0 : 0 ≤ Ene := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - respRho γ := by linarith only [hrho]
    rw [hcdef]
    positivity
  have hSums0 : 0 ≤ Sums := by
    have h1 : 0 ≤ weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
        (respCoeffPlus F a) := weakCellSum_nonneg _ _ _ _ _
    have h2 : 0 ≤ weakAverageSum (respGrid jStar F) t H (respRho γ)
        (respEhatPlus P jStar F t) (respCoeffPlus F a) := weakAverageSum_nonneg _ _ _ _ _ _
    rw [hSumsdef]
    have : 0 ≤ 16 * K * L := by positivity
    exact mul_nonneg this (by linarith only [h1, h2])
  have hMnn : 0 ≤ respAllScaleMax P γ jStar F t a := by
    have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
      fun _ => Real.sInf_nonneg fun _ hx => hx.1
    refine Real.sSup_nonneg ?_
    rintro y ⟨m, z, _hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)
  have hgood' : respAllScaleMax P γ jStar F t a ≤ 1 →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
        ≤ Sums + c * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) * Ene := by
    intro hMle
    have hhead := h6a_recentHead_carrier_plus P γ _hγ jStar H F t e hgrid hint a hbdd u hu hMle
    have hhead' : (∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffPlus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffPlus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u))))) ≤ Sums := hhead
    have := hgood hMle
    linarith only [this, hhead']
  have hbad' : 1 < respAllScaleMax P γ jStar F t a →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
        ≤ c * Real.sqrt (respAllScaleMax P γ jStar F t a) * Ene := by
    intro hMgt
    have := hbad hMgt
    linarith only [this]
  have hkey := h6a_head_branchfree _hγ H hMnn
    ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
      besovSeminorm t (fun n w =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
            cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
    Sums Ene c c hc0 hc0 hSums0 hEne0 hgood' hbad'
  rwa [max_self] at hkey

end

end Homogenization.HighContrast.Multiscale
