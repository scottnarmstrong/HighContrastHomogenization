/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowBlock
import HCPoly.Provider.Response.ProfileDefectCarriers
import HCPoly.Provider.Response.ConstantSkewBlock

/-!
# Fixed-skew all-earlier response-row carriers

The response profile is written for the recentered coefficient.  Its annealed
blocks are therefore the common shear congruences of the original annealed
blocks.  Coefficient transposition is applied only after this congruence.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The hatted block `G_hᵀ H G_h`. -/
def profileHattedBlock (h : Mat d) (H : BlockMat d) : BlockMat d :=
  skewBlockCongr h H

/-- The coefficient-transpose image of a hatted block. -/
def profileHattedAdjointBlock (h : Mat d) (H : BlockMat d) : BlockMat d :=
  profileAdjointBlock (profileHattedBlock h H)

/-- The hatted terminal block is the recentered adapted mean. -/
theorem profileHattedBlock_adaptedMean (P : Measure (CoeffSpace d))
    (q h : Mat d) (k : ℤ) :
    profileHattedBlock h (adaptedMean P q k) =
      profileRecenteredMean P q h k := by
  apply toFullBlockMat_injective
  simp only [profileHattedBlock, toFullBlockMat_skewBlockCongr,
    profileRecenteredMean, toFullBlockMat_blockMatMul,
    toFullBlockMat_blockMatTranspose_conj, toFullBlockMat_blockG]
  rw [Matrix.mul_assoc]

/-- The hatted adjoint terminal block is the recentered adjoint mean. -/
theorem profileHattedAdjointBlock_adaptedMean
    (P : Measure (CoeffSpace d)) (q h : Mat d) (k : ℤ) :
    profileHattedAdjointBlock h (adaptedMean P q k) =
      profileRecenteredAdjointMean P q h k := by
  rw [profileHattedAdjointBlock, profileRecenteredAdjointMean,
    profileHattedBlock_adaptedMean]
  rfl

/-- A finite lower-cutoff primal row of hatted Schur loads. -/
def profilePrimalHattedRowPartial (P : Measure (CoeffSpace d))
    (q h : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d) : ℝ :=
  ∑ k ∈ Finset.Icc Klo s,
    profileRowWeight k s *
      avsum (alignedIndex q k s) (fun w ↦
        profileSchurLoad
          (profileHattedBlock h
            (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen)

/-- A finite lower-cutoff coefficient-transpose row of hatted Schur loads. -/
def profileAdjointHattedRowPartial (P : Measure (CoeffSpace d))
    (q h : Mat d) (Klo s : ℤ) (Pcen Qcen : Vec d) : ℝ :=
  ∑ k ∈ Finset.Icc Klo s,
    profileRowWeight k s *
      avsum (alignedIndex q k s) (fun w ↦
        profileSchurLoad
          (profileHattedAdjointBlock h
            (annealedBlock P (adaptedCellAt q k w))) Pcen Qcen)

/-- The primal all-earlier hatted row.  Divergence is represented by `⊤`. -/
def profilePrimalHattedEarlierRow (P : Measure (CoeffSpace d))
    (q h : Mat d) (s : ℤ) (Pcen Qcen : Vec d) : ℝ≥0∞ :=
  ⨆ Klo : ℤ,
    ENNReal.ofReal (profilePrimalHattedRowPartial P q h Klo s Pcen Qcen)

/-- The adjoint all-earlier hatted row.  Divergence is represented by `⊤`
independently of the primal row. -/
def profileAdjointHattedEarlierRow (P : Measure (CoeffSpace d))
    (q h : Mat d) (s : ℤ) (Pcen Qcen : Vec d) : ℝ≥0∞ :=
  ⨆ Klo : ℤ,
    ENNReal.ofReal (profileAdjointHattedRowPartial P q h Klo s Pcen Qcen)

end

end Homogenization.HighContrast.Response
