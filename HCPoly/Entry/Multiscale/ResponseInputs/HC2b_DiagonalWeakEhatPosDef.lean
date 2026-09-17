import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakMeanPosDef

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The block shear `⟨1, 0, c, 1⟩` written in flat `fromBlocks` form.  It is lower
unitriangular, so its determinant is `1`. -/
private theorem h6a_shear_full (c : Mat d) :
    toFullBlockMat (⟨1, 0, c, 1⟩ : BlockMat d) = Matrix.fromBlocks (1 : Mat d) 0 c 1 := by
  ext (i | i) (j | j) <;> rfl

/-- The response shear `G = ⟨1, 0, respg F, 1⟩` is a unit for every `F`, with no hypothesis:
the shear by `-respg F` is a right inverse, so the determinant is a unit. -/
theorem h6a_isUnit_toFullBlockMat_respG (F : BlockMat d) :
    IsUnit (toFullBlockMat (respG F)) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse
      (B := toFullBlockMat (⟨1, 0, -(respg F), 1⟩ : BlockMat d)) ?_)
  rw [respG, h6a_shear_full, h6a_shear_full, Matrix.fromBlocks_multiply]
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, add_neg_cancel,
    Matrix.fromBlocks_one]

/-- The doubling `D = diag(Id, -Id)` written in flat `fromBlocks` form. -/
private theorem h6a_blockD_full :
    toFullBlockMat (blockD d) = Matrix.fromBlocks (1 : Mat d) 0 0 (-1) := by
  ext (i | i) (j | j) <;> rfl

/-- The doubling `D = diag(Id, -Id)` is its own inverse, hence a unit. -/
private theorem h6a_isUnit_blockD : IsUnit (toFullBlockMat (blockD d)) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (B := toFullBlockMat (blockD d)) ?_)
  rw [h6a_blockD_full, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, add_zero, zero_add, neg_mul_neg, Matrix.fromBlocks_one,
    Matrix.one_mul]

/-- Congruence by a unit preserves positive definiteness: conjugating a positive definite
matrix by an invertible matrix keeps it positive definite (`p.response.transfer`). -/
theorem h6a_blockCongr_posDef {G E : BlockMat d} (hG : IsUnit (toFullBlockMat G))
    (hE : (toFullBlockMat E).PosDef) : (toFullBlockMat (blockCongr G E)).PosDef := by
  rw [blockCongr, toFullBlockMat_ofFullBlockMat]
  have h := hE.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hG)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The negative response sample `Ehat^- = Gᵗ E_t G` is positive definite as soon as the
mean `E_t` is, since the shear `G` is a unit (`p.response.transfer`). -/
theorem h6a_respEhatMinus_posDef_of_mean {P : Measure (CoeffSpace d)} {jStar : ℕ}
    {F : BlockMat d} {t : ℤ} (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
  h6a_blockCongr_posDef (h6a_isUnit_toFullBlockMat_respG F) hE

/-- The positive response sample `Ehat^+ = D Ehat^- D` is positive definite as soon as the
mean is, since the doubling `D` is a unit (`p.response.transfer`). -/
theorem h6a_respEhatPlus_posDef_of_mean {P : Measure (CoeffSpace d)} {jStar : ℕ}
    {F : BlockMat d} {t : ℤ} (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
  h6a_blockCongr_posDef h6a_isUnit_blockD (h6a_respEhatMinus_posDef_of_mean hE)

/-- **The response sample is positive definite as soon as the coarse block is law-integrable.**
Composing the congruence step with `h6a_respMean_posDef_of_integrable`, the positive definiteness
that the recent-head chain asks of `Ê⁻` rests on exactly two things a caller can hold: the unit
selected grid that the cell-average estimate already carries, and the integrability of the coarse
block under the law.  Neither stationarity, nor the coarse-ellipticity bundle, nor a dimension
bound is used. -/
theorem h6a_respEhatMinus_posDef_of_integrable [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) (t : ℤ)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
  h6a_respEhatMinus_posDef_of_mean (h6a_respMean_posDef_of_integrable hgrid t hint)

/-- The adjoint twin of `h6a_respEhatMinus_posDef_of_integrable`. -/
theorem h6a_respEhatPlus_posDef_of_integrable [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) (t : ℤ)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
  h6a_respEhatPlus_posDef_of_mean (h6a_respMean_posDef_of_integrable hgrid t hint)

end

end Homogenization.HighContrast.Multiscale
