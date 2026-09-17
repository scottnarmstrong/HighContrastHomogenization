import HCPoly.Entry.Source.BoundedWindowFiniteness
import HCPoly.Entry.Setup.NormalizedFluctuation

/-!
# Finite positive adapted expectations

The actual law integrability uses arbitrary finite moments, with an auxiliary
bounded window. No original-window containment or fixed-Q source threshold is needed
for ordinary support lemmas. Source-facing consumers retain the source lower scale.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean annealedBlock
  blockMatEntry_annealedBlock blockPosDef_annealedBlock isSymmetricBlockMat_coarseBlockMatrix)
open Homogenization.HighContrast (adaptedCellTranslate)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory Geometry

noncomputable section

/-- Every entry of an actual adapted coarse block is law integrable. -/
theorem hasIntegrableCoarseBlock_adapted (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) (y : Vec d) :
    HasIntegrableCoarseBlock P (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) := by
  exact (Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
    jStar hjStar m hm j y 1 le_rfl).integrable_entry le_rfl

/-- Symmetry of the actual annealed block follows entrywise from sample symmetry. -/
theorem isSymmetricBlockMat_annealedBlock {d : ℕ}
    (P : Measure (CoeffSpace d)) (U : Set (Vec d)) :
    IsSymmetricBlockMat (annealedBlock P U) := by
  intro α β
  simp only [blockMatEntry_annealedBlock]
  exact integral_congr_ae (ae_of_all P fun a =>
    isSymmetricBlockMat_coarseBlockMatrix U (⇑a.1) α β)

/-- Symmetry and strict positivity on the CG block carrier give full matrix PosDef. -/
theorem fullBlock_posDef_of_pos {d : ℕ} {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hpos : Book.Ch02.BlockPosDef A) :
    (toFullBlockMat A).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(Analysis.toFullBlockMat_isHermitian_iff A).2 hA, ?_⟩
  intro x hx
  have hne : ofFullBlockVec x ≠ 0 := by
    intro hzero
    apply hx
    have hz := congrArg toFullBlockVec hzero
    rw [toFullBlockVec_ofFullBlockVec] at hz
    funext i
    have hi := congrFun hz i
    cases i <;> simpa [toFullBlockVec] using hi
  have hp := hpos (ofFullBlockVec x) hne
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockVec_ofFullBlockVec] at hp
  simpa only [star_trivial] using hp

/-- Full positive definiteness of the actual adapted annealed means, at every
integer generation, from the standing stationary dagger law. -/
theorem adaptedMean_posDef (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    (toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) j)).PosDef := by
  let : NeZero d := ⟨by omega⟩
  have hint := hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
    jStar hjStar m hm j 0
  have hpos := blockPosDef_annealedBlock hint (fun a =>
    blockPosDef_coarseBlock_adapted (explicitRoundedGrid jStar m)
      (isUnit_roundedGrid hjStar hm) j 0 a)
  have hp := fullBlock_posDef_of_pos
    (isSymmetricBlockMat_annealedBlock P _) hpos
  simpa [adaptedCellTranslate, adaptedMean, HighContrast.adaptedCell,
    HighContrast.centeredCube] using hp

end

end Homogenization.HighContrast.Annealed
