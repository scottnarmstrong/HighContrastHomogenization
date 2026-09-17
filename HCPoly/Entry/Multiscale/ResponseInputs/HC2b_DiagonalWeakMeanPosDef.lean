import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import HCPoly.Entry.Annealed.AdaptedIntegrability

/-!
# Positive definiteness of the annealed adapted mean from integrability alone

Every step of the cell-average estimate that consumes the response sample needs
`(toFullBlockMat (respMean P jStar F t)).PosDef`, and that reduces by definition to
`(toFullBlockMat (adaptedMean P (respGrid jStar F) t)).PosDef`.  The tree previously obtained
this only from `Annealed.adaptedMean_posDef`, which carries the whole coarse-ellipticity
bundle; but the pathwise positivity of the coarse block uses nothing beyond `IsUnit q`, and the
only genuinely missing input is the law-integrability of the coarse block.  The two theorems
below isolate that input, in the shape of the determinant bound
`1 ≤ (toFullBlockMat (adaptedMean P q j)).det`.

`IsProbabilityMeasure P` is not positivity content: it is the hypothesis under which the tree
proves `blockPosDef_annealedBlock` (its expectation argument ends in `measure_univ = 1`), and
`blockPosDef_coarseBlock_adapted` hides no ellipticity hypothesis — the local uniform
ellipticity is carried by `CoeffSpace d` itself, and the only extra ingredient is `IsUnit q`,
which the statement's hypothesis records.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean
  blockPosDef_annealedBlock coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The adapted annealed mean is positive definite as soon as its coarse block is
law-integrable: `IsUnit q` supplies the pathwise positivity, and the expectation of an
integrable family of positive blocks is positive. -/
theorem h6a_adaptedMean_posDef_of_integrable {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (hint : HasIntegrableCoarseBlock P (HighContrast.adaptedCell q j)) :
    (toFullBlockMat (adaptedMean P q j)).PosDef := by
  let U := HighContrast.adaptedCell q j
  have hp (a : CoeffSpace d) : Book.Ch02.BlockPosDef (coarseBlock U a) := by
    simpa [U, HighContrast.adaptedCellTranslate] using
      Annealed.blockPosDef_coarseBlock_adapted q hq j 0 a
  exact Annealed.fullBlock_posDef_of_pos (Annealed.isSymmetricBlockMat_annealedBlock P U)
    (blockPosDef_annealedBlock hint hp)

/-- The response mean inherits the same positive definiteness, since `respMean` and `respCell`
are `adaptedMean` and `HighContrast.adaptedCell` at the selected grid. -/
theorem h6a_respMean_posDef_of_integrable {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) (t : ℤ)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    (toFullBlockMat (respMean P jStar F t)).PosDef := by
  simpa only [respMean, respCell] using
    h6a_adaptedMean_posDef_of_integrable (P := P) hgrid t hint

end

end Homogenization.HighContrast.Multiscale
