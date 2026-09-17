import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH68a
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock

/-!
# The full entry family of the recentred coarse block on an aligned cell

The cell half of the cutoff-mean row of `p.response.transfer` reads the pathwise coarse block of
the recentred coefficients `a_- = a - g` and `a_+ = aᵀ + g` through three different functionals:
the two diagonal quadratic forms against the dual variable, the block response mean of the subcell
maximizer, which uses ALL four sub-blocks, and the stationarity collapse at the centred cell,
which asks only for measurability.  `HC3_RowsEntBridge` records the two diagonal sub-blocks; this
module records the whole entry family, in both the integrable and the measurable form, from the
same congruence bridge.

Recentring by a constant skew matrix field is a block congruence on an aligned adapted cell, so
every entry of the recentred block is a fixed real linear combination of the entries of the coarse
block of the sample; integrability is then `HasIntegrableCoarseBlock` and measurability is
unconditional.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The block entry is the entry of the flattened block. -/
private theorem blockMatEntry_eq_toFullBlockMat' {d : ℕ} (A : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry A α β = toFullBlockMat A α β := by
  cases α <;> cases β <;> rfl

/-- **Every entry of the recentred coarse block is integrable on an aligned cell, minus sign.**
The pathwise coarse block of `a_- = a - g` on an aligned adapted cell is the constant congruence
`Gᵀ 𝐀(V; a) G` of the coarse block of the sample, so each of its entries is a fixed real linear
combination of integrable functions. -/
theorem integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β) P :=
  integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (respG F) hint
    (fun a => h68_coarseBlockMatrix_respCoeffMinus_at hq j w F a)

/-- **Every entry of the recentred coarse block is integrable on an aligned cell, plus sign.**
The adjoint twin of `integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter`, with the congruence
`G_+ = G D` of the adjoint recentring. -/
theorem integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β) P :=
  integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (h68_respGPlus F) hint
    (fun a => h68_coarseBlockMatrix_respCoeffPlus_at hq j w F a)

/-- **Every entry of the recentred coarse block is measurable on an aligned cell, minus sign.**
No integrability is needed: the congruence bridge writes the entry as a fixed linear combination of
the entries of the coarse block of the sample, which are measurable outright. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β) P := by
  intro α β
  simpa only [blockMatEntry_eq_toFullBlockMat'] using
    (h68_measurable_coarseBlockMatrix_minus hq j w F α β).aestronglyMeasurable

/-- **Every entry of the recentred coarse block is measurable on an aligned cell, plus sign.**
The adjoint twin of `aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter`. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β) P := by
  intro α β
  simpa only [blockMatEntry_eq_toFullBlockMat'] using
    (h68_measurable_coarseBlockMatrix_plus hq j w F α β).aestronglyMeasurable

/-- **Measurability of the recentred coarse block at the centred cell, minus sign.**  The centred
cell is the aligned cell at index `0`, so the aligned statement applies verbatim.  This is the
`hmeasBlk` premise of the cell half of the cutoff-mean row. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCell {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffMinus F a)) α β) P := by
  intro α β
  simpa only [b130_adaptedCellAtCenter_zero q j] using
    aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter P hq j 0 F α β

/-- **Measurability of the recentred coarse block at the centred cell, plus sign.**  The adjoint
twin of `aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCell`. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCell {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffPlus F a)) α β) P := by
  intro α β
  simpa only [b130_adaptedCellAtCenter_zero q j] using
    aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter P hq j 0 F α β

end

end Homogenization.HighContrast.Multiscale
