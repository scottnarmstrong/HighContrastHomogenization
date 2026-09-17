import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportRows
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRespJIntegrable
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65a

/-!
# The annealed energies of the cutoff rows in closed block form

The cutoff rows of the response estimate bound the centred response with the two error scalars
`respEJMinus` and `respTauMinus`.  The first is the `P`-expectation of the recentred pathwise
response at one adapted cell; the second is the defect of that expectation between two scales.
Under the entrywise integrability of the coarse block carried by the cutoff rows, both are
algebraic functions of the recentred annealed block `respEhatMinus`: the pathwise response is the
block energy `x · A x / 2 - p · q'`, so its expectation is the same block energy of the annealed
block `E[A]`, and the pairing `p · q'` cancels in the defect.  These are the closed block forms
against which the cutoff rows are stated (`e.response.cutoff.estimate`).
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The `P`-expectation of the recentred pathwise response on an adapted cell `U_u` is the block
quadratic `½ x · E[A] x` of the recentred annealed block `respEhatMinus`, at the load
`x = (-p, q')`, minus the pairing `p · q'`.  This is the integral identity
`integral_respJ_eq_blockResponseEnergy` specialised to the recentred coefficient `a₋ = a - g`,
with its three inputs supplied by the coarse-block congruence, the entrywise transport of
integrability across that congruence, and the annealed-block identification
(`e.response.cutoff.estimate`, `e.annealed.schur`). -/
private theorem respIntegral_respCoeffMinus_eq_blockResponseEnergy {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (u : ℤ) (p q' : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) :
    (∫ a, respJ (respGrid jStar F) u p q' (respCoeffMinus F a) ∂P)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (respEhatMinus P jStar F u) (-p, q'))
        - vecDot p q' := by
  have hintA : HasIntegrableCoarseBlock P (HighContrast.adaptedCell (respGrid jStar F) u) := hint
  have hpath : ∀ a : CoeffSpace d,
      respJ (respGrid jStar F) u p q' (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, q')
            (blockMatVecMul
              (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffMinus F a))
              (-p, q'))
          - vecDot p q' :=
    fun a => respJ_respCoeffMinus_eq (respGrid jStar F) hq u F a p q'
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffMinus F a))
      α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
      (V := HighContrast.adaptedCell (respGrid jStar F) u) (b := respCoeffMinus F) hintA
      (fun a => coarseBlockMatrix_respCoeffMinus_eq_blockCongr (respGrid jStar F) hq u F a)
  have hann : annealedBlockOf P (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffMinus F)
      = respEhatMinus P jStar F u :=
    annealedBlockOf_respCoeffMinus_eq P jStar F u
      (fun a => hasQuadraticMu_adaptedCell (respGrid jStar F) hq u a) hint
  exact integral_respJ_eq_blockResponseEnergy P (respGrid jStar F) u p q'
    (respCoeffMinus F) (respEhatMinus P jStar F u) hpath hint' hann

/-- **The annealed energy of the cutoff minus rows as a block quadratic.**  Under entrywise
integrability of the coarse block, the `P`-expectation of the recentred pathwise response
`J(U_t, p, q⁻; a₋)` is the quadratic form `½ x · E[A] x` of the recentred annealed block
`respEhatMinus` at the load `x = (-p, q⁻)`, minus the pairing `p · q⁻`.  This is the closed block
form of the centred response energy `e.response.cutoff.estimate`. -/
theorem respEJMinus_eq_blockResponseEnergy {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respEJMinus P jStar F t e
      = (1 / 2 : ℝ) * blockVecDot
          (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
          (blockMatVecMul (respEhatMinus P jStar F t)
            (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e))
        - vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) := by
  unfold respEJMinus
  exact respIntegral_respCoeffMinus_eq_blockResponseEnergy P jStar F t
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) hq hint

end

end Homogenization.HighContrast.Multiscale
