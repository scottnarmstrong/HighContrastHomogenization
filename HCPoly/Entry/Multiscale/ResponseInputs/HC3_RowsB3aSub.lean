import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeOptimizerMean
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectRow1Cmp

/-!
# The optimizer mean identity on an aligned subcell at an almost-everywhere elliptic coefficient

The pathwise mean identity `AK.HC (2.32)` computes the cell mean of the doubled optimizer state of
a response maximizer as `x + R 𝐀(V) x` with `x = (-p, r)` and `𝐀(V)` the coarse block of the cell.
The response coefficients of `p.response.transfer` are elliptic only almost everywhere, while the
identity is available at a pointwise elliptic coefficient.  Carrying the harmonic field along an
almost everywhere elliptic representative preserves the maximizer property and the optimizer field
up to a null set, so the identity transfers verbatim to the aligned subcell.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The optimizer mean identity `AK.HC (2.32)` on an aligned adapted subcell `adaptedCellAtCenter q j w`,
at a coefficient `b` that agrees almost everywhere there with a pointwise elliptic representative
`f`: the cell average of the doubled optimizer field of any response maximizer is
`(-p, r) + R 𝐀(adaptedCellAtCenter q j w; b) (-p, r)`. -/
theorem cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q j w) f)
    (hae : b =ᵐ[volumeMeasureOn (adaptedCellAtCenter q j w)] f)
    (p r : Vec d) (v : AHarmonicFunction b (adaptedCellAtCenter q j w))
    (hv : IsResponseMaximizer (adaptedCellAtCenter q j w) p r b v) :
    cellAverage (adaptedCellAtCenter q j w) (optimizerField b v)
      = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter q j w) b) (-p, r) := by
  exact cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq j w)
    (volume_adaptedCellAtCenter_toReal_pos q hq j w) hEll hae p r v hv

end

end Homogenization.HighContrast.Multiscale
