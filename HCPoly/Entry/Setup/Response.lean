import HCPoly.Entry.Geometry.StandardCell
import HCPoly.Setup.BlockAlgebra
import HCPoly.Setup.LocalSigmaFields
import Homogenization.CoarseGraining.BlockMatrixProperties
import Homogenization.CoarseGraining.CoarseBounds
import HCPoly.Setup.Response
import HCPoly.Setup.CoefficientSpace

/-!
# The coarse block response and the annealed block

The coarse block response `𝐀(U; a)` of the paper is CoarseGraining's canonical
variational coarse block matrix of the sample field.  This file fixes it, its annealed
expectation, the intrinsic annealed contrast `Θ_m` (`e.Theta.m`), and the two definedness
guards the annealed block needs; and it records the facts that make the encoding honest: the
response depends only on the almost everywhere class of the field, its entries are the
variational quantities, it is symmetric, and its diagonal entries and basis-sum quadratic
forms are nonnegative.

The names and signatures reproduce those of the older `highcontrast-poly` development; the
bodies are re-derived here.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock)
namespace Homogenization.HighContrast

open MeasureTheory Geometry

noncomputable section

variable {d : ℕ}

/-! ## The coarse response -/

/-! ## The response depends only on the almost everywhere class -/

/-! ## Entries, symmetry, nonnegativity -/

/-! ## The annealed block is the entrywise expectation -/

/-- Integrability of the doubled quadratic form's entrywise terms over the law. -/
private theorem integrable_entry_term {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (X : BlockVec d) (α β : BlockCoord d) :
    Integrable (fun a => toFullBlockVec X α *
      (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β)) P :=
  ((hint α β).mul_const (toFullBlockVec X β)).const_mul _

end

end Homogenization.HighContrast
