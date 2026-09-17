import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCanPairMeas
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRespJPlus
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH68a
import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
import Homogenization.Internal.Ch02.Adapters
import Homogenization.Ambient.CoefficientField

/-!
# The unweighted quadratic readout of the canonical cutoff pairing

The cutoff pairing of `e.response.cutoff.estimate` expands into one quadratic term and three
linear terms (AK.HC Lemma A.1, (A.4)).  `HC3_CutoffSupportCanPairMeas` treats the three linear
terms, and `HC3_CutoffSupportQuadMeas` reduces the quadratic term to the cutoff-weighted block
self-pairing of the canonical optimizer state.

This file treats the unweighted quadratic readout, the full-cell energy of the canonical
optimizer,

`a ↦ volumeAverage (adaptedCell q t) (fun x => vecDot Z(a,x).1 Z(a,x).2)`,

where `Z(a,·)` is the canonical optimizer state.  The flux slot of that state is the recentred
coefficient applied to its gradient slot, so the integrand is the `a`-energy density
`⟨∇v, a ∇v⟩` of the canonical maximizer.  The full-cell average of that density is the doubled
maximizer energy, which is twice the pathwise response `J(adaptedCell q t, p, r)` of the
recentred coefficient.  The pathwise response is an explicit block quadratic of the coarse
block, hence a measurable function of the sample, so the unweighted quadratic readout is
measurable in the sample with no hypothesis beyond the cutoff class data.  This is the `φ = 1`
case of the quadratic term of the expansion.

The genuinely cutoff-weighted readout is local and is not the full-cell energy; its
measurability is the block self-pairing statement isolated in `HC3_CutoffSupportQuadMeas`.
-/

open Homogenization.HighContrast (CoeffSpace blockVecDot_blockMatVecMul_eq_sum
  toFullBlockMat_eq_blockMatEntry)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Measurability of the recentred pathwise responses -/

/-- The recentred minus pathwise response on an adapted cell is measurable in the sample.  It is
the explicit block quadratic of the recentred coarse block (AK.HC (2.15)), whose flattened
entries are measurable. -/
theorem measurable_respJ_respCoeffMinus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) :
    Measurable fun a : CoeffSpace d => respJ q t p r (respCoeffMinus F a) := by
  have hpath : (fun a : CoeffSpace d => respJ q t p r (respCoeffMinus F a))
      = fun a : CoeffSpace d =>
        (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r))
          - vecDot p r := by
    funext a
    exact respJ_respCoeffMinus_eq q hq t F a p r
  rw [hpath]
  have hentry : ∀ α β : BlockCoord d, Measurable fun a : CoeffSpace d =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell q t)
        (respCoeffMinus F a)) α β := by
    intro α β
    have h := h68_measurable_coarseBlockMatrix_minus (q := q) hq t 0 F α β
    simpa only [b130_adaptedCellAtCenter_zero, toFullBlockMat_eq_blockMatEntry] using h
  have hquad : Measurable fun a : CoeffSpace d =>
      blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r)) := by
    have hsum : (fun a : CoeffSpace d => blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r)))
        = fun a : CoeffSpace d => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec (-p, r) α *
              (blockMatEntry
                  (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) α β *
                toFullBlockVec (-p, r) β) := by
      funext a
      rw [blockVecDot_blockMatVecMul_eq_sum]
    rw [hsum]
    exact Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ =>
        ((hentry α β).mul_const _).const_mul _
  exact (hquad.const_mul (1 / 2 : ℝ)).sub measurable_const

/-- The recentred plus pathwise response on an adapted cell is measurable in the sample.  It is
the explicit block quadratic of the adjoint recentred coarse block, whose flattened entries are
measurable. -/
theorem measurable_respJ_respCoeffPlus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) :
    Measurable fun a : CoeffSpace d => respJ q t p r (respCoeffPlus F a) := by
  have hpath : (fun a : CoeffSpace d => respJ q t p r (respCoeffPlus F a))
      = fun a : CoeffSpace d =>
        (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r))
          - vecDot p r := by
    funext a
    exact respJ_respCoeffPlus_eq q hq t F a p r
  rw [hpath]
  have hentry : ∀ α β : BlockCoord d, Measurable fun a : CoeffSpace d =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell q t)
        (respCoeffPlus F a)) α β := by
    intro α β
    have h := h68_measurable_coarseBlockMatrix_plus (q := q) hq t 0 F α β
    simpa only [b130_adaptedCellAtCenter_zero, toFullBlockMat_eq_blockMatEntry] using h
  have hquad : Measurable fun a : CoeffSpace d =>
      blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r)) := by
    have hsum : (fun a : CoeffSpace d => blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r)))
        = fun a : CoeffSpace d => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec (-p, r) α *
              (blockMatEntry
                  (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) α β *
                toFullBlockVec (-p, r) β) := by
      funext a
      rw [blockVecDot_blockMatVecMul_eq_sum]
    rw [hsum]
    exact Finset.measurable_sum Finset.univ fun α _ =>
      Finset.measurable_sum Finset.univ fun β _ =>
        ((hentry α β).mul_const _).const_mul _
  exact (hquad.const_mul (1 / 2 : ℝ)).sub measurable_const

/-! ## The full-cell quadratic readout as twice the pathwise response -/

/-! ## The unweighted quadratic readouts as pathwise responses -/

/-! ## Measurability of the unweighted quadratic readouts -/

end

end Homogenization.HighContrast.Multiscale
