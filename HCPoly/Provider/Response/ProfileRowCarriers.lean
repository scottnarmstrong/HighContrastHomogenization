/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileCarriers
import HCPoly.Geometry.DeterminantLoss
import HCPoly.Provider.Initialization.Boundary
import HCPoly.Provider.Transport.WindowMomentBound
import Homogenization.Book.Ch02.Block

/-!
# All-earlier response-row carriers

This file records the Schur load, its finite lower-cutoff rows, the fail-closed
all-earlier row, and the response-row constant assembled from the drift and the
source row.  The adjoint block is the coefficient-transpose sign congruence; it
is distinct from the sharp block reflection used by source control.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The coefficient-transpose image of a doubled response block. -/
def profileAdjointBlock (H : BlockMat d) : BlockMat d :=
  blockMatMul (blockDiag 1 (-1))
    (blockMatMul H (blockDiag 1 (-1)))

/-- The geometric response-row weight at scale `k` relative to `s`. -/
def profileRowWeight (k s : ℤ) : ℝ :=
  (3 : ℝ) ^ (3 / 2 * ((k : ℝ) - (s : ℝ)))

/-- The Schur diagonal load of a block at a pair of independent centers.
The two actual carriers are the top-left block and `schurSigmaStar`; the
inverse square root in the second slot is therefore written literally. -/
def profileSchurLoad (H : BlockMat d) (Pcen Qcen : Vec d) : ℝ :=
  (Book.Ch02.vecNorm
      (matVecMul (matSqrt ((schurSigmaStar H)⁻¹)) Qcen) +
    Book.Ch02.vecNorm (matVecMul (matSqrt H.upperLeft) Pcen)) ^ 2

/-- The two diagonal quadratic forms comprising the row load. -/
def profileQuadraticLoad (H : BlockMat d) (Pcen Qcen : Vec d) : ℝ :=
  blockVecDot ((Pcen, 0) : BlockVec d)
      (blockMatVecMul H ((Pcen, 0) : BlockVec d)) +
    blockVecDot ((0, Qcen) : BlockVec d)
      (blockMatVecMul H ((0, Qcen) : BlockVec d))

/-- The cap-two response coefficient `Γ_s^ᵎ`. -/
def profileRowGamma (P : Measure (CoeffSpace d)) (rhoDr : ℝ) (q : Mat d)
    (Cd g : ℝ) (E : BlockMat d) (jStar : ℤ) (m0 : Mat d) (s : ℤ) : ℝ :=
  (1 + linearDrift P rhoDr q jStar s) /
      (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) +
    kappaRef E * boundaryConst Cd g m0 ^ 2 * 2 ^ 2 /
        ((3 : ℝ) ^ (3 / 2 - g) - 1) *
      (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ)))

theorem profileRowGamma_eq (P : Measure (CoeffSpace d)) (rhoDr : ℝ)
    (q : Mat d) (Cd g : ℝ) (E : BlockMat d) (jStar : ℤ)
    (m0 : Mat d) (s : ℤ) :
    profileRowGamma P rhoDr q Cd g E jStar m0 s =
      (1 + linearDrift P rhoDr q jStar s) /
          (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) +
        kappaRef E * boundaryConst Cd g m0 ^ 2 * 2 ^ 2 /
            ((3 : ℝ) ^ (3 / 2 - g) - 1) *
          (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) := rfl

end

end Homogenization.HighContrast.Response
