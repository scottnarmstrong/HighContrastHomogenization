/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.RoundedOuterCellEnclosure
import HCPoly.Provider.Regularity.RoundedOuterScaleFubini
import HCPoly.Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity
import HCPoly.Provider.Entry.AdapterQuadratic
import HCPoly.Provider.Regularity.RoundedNormalizedRootCellResponseMax
import HCPoly.Provider.PolynomialHomogenization.NormalizedRootCoefficient
import HCPoly.Provider.Regularity.RoundedAffineMap
import HCPoly.Provider.Transport.WhitneyRows
import HCPoly.Provider.Response.AdaptedLinearOscillation
import HCPoly.Provider.Regularity.GoodTail
import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# Spatial maxima of normalized physical responses on rounded outer cells

At every aligned base-rounded cell, the physical response is maximized over
the unit identity-reference loading.  The finite spatial maximum at each
depth is then controlled by one normalized-root parent response row, with the
rounded boundary and parent-shift factors explicit.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped BigOperators Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The physical doubled response on one aligned base-rounded cell, maximized
over loads whose exact normalized-reference images are the same unit vector. -/
noncomputable def baseRoundedNormalizedDoubledResponseMaxAt
    [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (_hS : (symmPart abar).PosDef) (k : ℤ) (w : Fin d → ℤ) : ℝ :=
  sSup {r : ℝ | ∃ e : FullBlockVec d, ∃ P Q : BlockVec d,
    Book.Ch02.fullBlockVecNormSq e = 1 ∧
      normalizedReferencePrimalLoad abar P = ofFullBlockVec e ∧
      normalizedReferenceDualLoad abar Q = ofFullBlockVec e ∧
      r = coeffSpaceDoubledResponse
        (adaptedCellAt (baseRoundedGrid (symmPart abar)) k w) a P Q}

private theorem constantFullBlockMatrixSqrt_one [NeZero d] :
    Book.Ch02.constantFullBlockMatrixSqrt (1 : Mat d) = 1 := by
  have hone : (1 : Mat d) = scalarMatrix (d := d) 1 := by
    ext i j
    simp [scalarMatrix, Matrix.one_apply]
  have hblock : Book.Ch02.constantBlockMatrix (1 : Mat d) =
      Book.Ch02.blockIdentity d := by
    rw [hone, Book.Ch02.constantBlockMatrix_scalarMatrix one_pos]
    apply blockMat_ext <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, scalarMatrix]
  unfold Book.Ch02.constantFullBlockMatrixSqrt
  rw [show Book.Ch02.constantFullBlockMatrix (1 : Mat d) = 1 by
    unfold Book.Ch02.constantFullBlockMatrix
    rw [hblock]
    exact toFullBlockMat_blockIdentity]
  exact CFC.sqrt_one

end

end Transport
end HighContrast
end Homogenization
