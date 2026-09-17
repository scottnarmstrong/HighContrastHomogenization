import HCPoly.Entry.Annealed.MeanOrder
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportEnergies
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportRows

/-!
# Entrywise integrability of the recentred coarse block on an aligned cell

The cell half of the cutoff-mean row of `p.response.transfer` needs, on every coarse subcell, the
`P`-integrability of the individual entries of the pathwise coarse block of the recentred
coefficients `a_- = a - g` and `a_+ = aᵀ + g`.  Recentring by a constant skew matrix is a block
congruence, so those entries are fixed real linear combinations of the entries of the coarse block
of the sample itself, which `HasIntegrableCoarseBlock` supplies.  This module records that
integrability for the four sub-block entries used by the annealed heads, together with the
`AEStronglyMeasurable` forms at the centred cell that the stationarity collapse consumes.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise coarse block of `a_- = a - g` on an aligned adapted cell is the constant shear
congruence `Gᵀ 𝐀(U; a) G` of the sample's coarse block.  The recentring subtracts the constant
skew matrix field `g`, so the variational quantity is recovered by the shear congruence
(`e.annealed.schur`) once quadraticity holds on the cell. -/
private theorem coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter_eq_blockCongr
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)
      = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q j w) a) := by
  have hquad : HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) := by
    simpa only [adaptedCellAtCenter] using
      h7_hasQuadraticMu_adaptedCellTranslate q hq j (adaptedCellCenter q j w) a
  exact coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
    (a := (⇑a.1 : CoeffField d)) (g := respg F) (respg_isSkew F) hquad

/-- The pathwise coarse block of `a_+ = aᵀ + g` on an aligned adapted cell is the constant
congruence `D Gᵀ 𝐀(U; a) G D` of the sample's coarse block, with `D` the flux-sign block and `G`
the shear of `respG`.  The adjoint recentring is the composition of the flux flip with the shear
congruence, so the two congruences compose to one constant congruence. -/
private theorem coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter_eq_blockCongr
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)
      = blockCongr (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
          (coarseBlock (adaptedCellAtCenter q j w) a) := by
  have hquad : HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) := by
    simpa only [adaptedCellAtCenter] using
      h7_hasQuadraticMu_adaptedCellTranslate q hq j (adaptedCellCenter q j w) a
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = -matTranspose (respg F) := by
      simp only [matTranspose, Matrix.transpose_neg]
    rw [hT, respg_isSkew F]
  have h1 : respCoeffPlus F a
      = fun y => (adjointCoeffField (⇑a.1 : CoeffField d)) y - (-(respg F)) := by
    funext y
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
    (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
    (hasQuadraticMu_adjointCoeffField hquad)
  have h3 : coarseBlockMatrix (adaptedCellAtCenter q j w)
        (adjointCoeffField (⇑a.1 : CoeffField d))
      = blockCongr (blockD d) (coarseBlock (adaptedCellAtCenter q j w) a) := by
    rw [coarseBlockMatrix_adjointCoeffField_of_exists
      (exists_coarseBlockMatrix_of_hasQuadraticMu hquad), ← blockCongr_blockD]
    rfl
  rw [h1, h2, h3, blockCongr_blockCongr]
  exact congrArg (fun M => blockCongr M (coarseBlock (adaptedCellAtCenter q j w) a))
    (congrArg ofFullBlockMat (blockD_mul_shear_neg (respg F)))

/-- Entrywise integrability of the recentred coarse block `a_- = a - g` on an aligned cell: each
`blockMatEntry` is a fixed real linear combination of the entries of the coarse block of the
sample, hence `P`-integrable by `HasIntegrableCoarseBlock`. -/
private theorem integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)} (q : Mat d) (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β) P :=
  integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
    (V := adaptedCellAtCenter q j w) (b := respCoeffMinus F) hint
    (fun a => coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter_eq_blockCongr q hq j w F a)

/-- Entrywise integrability of the adjoint recentred coarse block `a_+ = aᵀ + g` on an aligned
cell: each `blockMatEntry` is a fixed real linear combination of the entries of the coarse block
of the sample, hence `P`-integrable by `HasIntegrableCoarseBlock`. -/
private theorem integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)} (q : Mat d) (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β) P :=
  integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr
    (G := ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
    (V := adaptedCellAtCenter q j w) (b := respCoeffPlus F) hint
    (fun a => coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter_eq_blockCongr q hq j w F a)

/-- **Integrability of the upper-left block of the recentred coarse block.**  For the unit grid
`q = respGrid jStar F`, a scale `j` and an aligned cell index `w`, if every entry of the coarse
block of the sample is `P`-integrable there, then every entry of the upper-left sub-block of the
pathwise coarse block of `a_- = a - g` is `P`-integrable. -/
theorem integrable_coarseBlockMatrix_upperLeft_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)).upperLeft i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq j w F hint
      (Sum.inl i) (Sum.inl k)

/-- **Integrability of the lower-right block of the recentred coarse block.**  The lower-right twin
of `integrable_coarseBlockMatrix_upperLeft_respCoeffMinus`. -/
theorem integrable_coarseBlockMatrix_lowerRight_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)).lowerRight i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq j w F hint
      (Sum.inr i) (Sum.inr k)

/-- **Integrability of the upper-left block of the adjoint recentred coarse block.**  For the unit
grid `q = respGrid jStar F`, a scale `j` and an aligned cell index `w`, if every entry of the
coarse block of the sample is `P`-integrable there, then every entry of the upper-left sub-block
of the pathwise coarse block of `a_+ = aᵀ + g` is `P`-integrable. -/
theorem integrable_coarseBlockMatrix_upperLeft_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)).upperLeft i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq j w F hint
      (Sum.inl i) (Sum.inl k)

/-- **Integrability of the lower-right block of the adjoint recentred coarse block.**  The
lower-right twin of `integrable_coarseBlockMatrix_upperLeft_respCoeffPlus`. -/
theorem integrable_coarseBlockMatrix_lowerRight_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)).lowerRight i k) P := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  intro i k
  simpa only [blockMatEntry] using
    integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq j w F hint
      (Sum.inr i) (Sum.inr k)

end

end Homogenization.HighContrast.Multiscale
