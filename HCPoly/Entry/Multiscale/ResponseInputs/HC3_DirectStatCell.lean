import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportRows
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportEnergies
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH68a
import HCPoly.Entry.Annealed.MeanOrder

/-!
# The annealed response is the same on every aligned subcell

The mean cancellation behind `p.response.transfer` — the constant cell means cancel after
expectation because the scale-`s` translations are integral — rests on the statement that,
for a stationary law, the annealed response of a recentred coefficient family on an aligned
cell of a fixed scale is independent of the particular aligned cell.  The aligned cells of a
scale are integer translates of the centred cell, the annealed block of a translate is the
annealed block of the scale, and the pathwise response on any aligned cell is the block energy
of that cell's coarse block; hence the expectation is a function of the scale alone.

This module records that identity for both recentred families `a_-` and `a_+`.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  blockVecDot_blockMatVecMul_eq_sum coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Stationary aligned cells have a scale-determined annealed response, minus sign.**  For a
stationary law `P` and the recentred coefficient `a_- = a - g` of `p.response.transfer`, the
`P`-expectation of the pathwise response on the aligned cell `adaptedCellAtCenter (respGrid jStar F) j w`
is the block energy of the annealed block `Gᵀ E_j G`, independently of the cell index `w`. -/
theorem integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffMinus F a) ∂P)
      = blockResponseEnergy (blockCongr (respG F) (respMean P jStar F j)) p r := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter (respGrid jStar F) j w) (⇑a.1 : CoeffField d) :=
    fun a => by
      simpa only [adaptedCellAtCenter] using
        h7_hasQuadraticMu_adaptedCellTranslate (respGrid jStar F) hq j
          (adaptedCellCenter (respGrid jStar F) j w) a
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F a)
        = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) j w) a) :=
    fun a => coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter (respGrid jStar F) j w)
      (a := (⇑a.1 : CoeffField d)) (g := respg F) (respg_isSkew F) (hquad a)
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F a))
              (-p, r))
          - vecDot p r :=
    fun a => h6a_responseJ_adaptedCellAtCenter_respCoeffMinus (respGrid jStar F) hq j w F a p r
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
      (V := adaptedCellAtCenter (respGrid jStar F) j w) (b := respCoeffMinus F) hint hb
  have hann : annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F)
      = blockCongr (respG F) (respMean P jStar F j) := by
    rw [annealedBlockOf_eq_blockCongr (respG F) (respCoeffMinus F) hint hb]
    congr 1
    have h := Annealed.annealedBlock_adaptedCellAtCenter P hstat jStar hjStar (explicitCanonicalMetric F) hm j hj w
    simpa [respGrid, respMean] using h
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
          (respCoeffMinus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hQ := integral_blockVecDot_blockMatVecMul_coarseBlockMatrix P
    (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F) (-p, r) hint'
  have huniv : P.real Set.univ = 1 := by simp
  simp only [blockResponseEnergy, hpath]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv, one_smul]

/-- **Stationary aligned cells have a scale-determined annealed response, plus sign.**  For a
stationary law `P` and the recentred coefficient `a_+ = aᵀ + g` of `p.response.transfer`, the
`P`-expectation of the pathwise response on the aligned cell `adaptedCellAtCenter (respGrid jStar F) j w`
is the block energy of the annealed block `G_+ᵀ E_j G_+`, independently of the cell index `w`. -/
theorem integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffPlus F a) ∂P)
      = blockResponseEnergy (blockCongr (h68_respGPlus F) (respMean P jStar F j)) p r := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F a)
        = blockCongr (h68_respGPlus F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) j w) a) :=
    fun a => h68_coarseBlockMatrix_respCoeffPlus_at hq j w F a
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffPlus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F a))
              (-p, r))
          - vecDot p r :=
    fun a => h6a_responseJ_adaptedCellAtCenter_respCoeffPlus (respGrid jStar F) hq j w F a p r
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := h68_respGPlus F)
      (V := adaptedCellAtCenter (respGrid jStar F) j w) (b := respCoeffPlus F) hint hb
  have hann : annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F)
      = blockCongr (h68_respGPlus F) (respMean P jStar F j) := by
    rw [annealedBlockOf_eq_blockCongr (h68_respGPlus F) (respCoeffPlus F) hint hb]
    congr 1
    have h := Annealed.annealedBlock_adaptedCellAtCenter P hstat jStar hjStar (explicitCanonicalMetric F) hm j hj w
    simpa [respGrid, respMean] using h
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
          (respCoeffPlus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hQ := integral_blockVecDot_blockMatVecMul_coarseBlockMatrix P
    (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F) (-p, r) hint'
  have huniv : P.real Set.univ = 1 := by simp
  simp only [blockResponseEnergy, hpath]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv, one_smul]

end

end Homogenization.HighContrast.Multiscale
