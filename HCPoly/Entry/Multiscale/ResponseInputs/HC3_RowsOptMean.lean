import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECoeff
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeOptimizerMean
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarmH7Helpers

/-!
# The optimizer-mean identity `E[(X_{u_t})_{U_t}] = Y^∓`

In `p.response.transfer` the annealed mean `Y^∓` of AK.HC (2.32) is *defined* through the block
formula `Y = (I + R Ehat_t^∓) x^∓`.  This module shows that the block formula really is the
expectation of the cell average of the doubled optimizer state `X = (∇v, a_∓ ∇v)` of the
terminal cell: `E[(X_{u_t})_{U_t}] = Y^∓`.

The argument is affine.  Pathwise the cell average of the optimizer state is
`x + R 𝐀(U_t; a_∓) x`, with `𝐀` the set-level coarse block matrix; `blockResponseMean` is
affine in the entries of the block, so integrating the entrywise affine expression reproduces the
same formula with the annealed block `Ehat_t^∓` in place of the pathwise one.  The sample
coefficient `a_∓` is only almost everywhere elliptic, so the pathwise identity is applied to an
elliptic representative and transported back along the almost everywhere agreement of the
optimizer fields and of the coarse block matrices.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-- The annealed mean `Y^-` of AK.HC (2.32) is the expectation of the cell average of the
doubled optimizer state of the terminal cell: `E[(X_{u_t})_{U_t}] = Y^-`, for any measurable
selection `a ↦ u_t(a)` of response maximizers.  The pathwise identity is applied to an
almost everywhere elliptic representative of `a_- = a - g`, and the resulting statement is
transported back along the almost everywhere agreement of the two optimizer fields and of the
two coarse block matrices. -/
theorem respYMinus_eq_integral_cellAverage_optimizerField {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (hF : (toFullBlockMat F).PosDef)
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (huM : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) :
    respYMinus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P)) := by
  have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (respCell jStar F t) (⇑a.1 : CoeffField d) := by
    intro a
    simpa only [respCell, adaptedCellTranslate_zero] using
      h7_hasQuadraticMu_adaptedCellTranslate (respGrid jStar F) hgrid t 0 a
  have hgskew : matTranspose (respg F) = -(respg F) := respCalib_respg_isSkew hF
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)
        = blockCongr (respG F) (coarseBlock (respCell jStar F t) a) := fun a =>
    coarseBlockMatrix_sub_skew_eq_blockCongr hgskew (hquad a)
  have hA : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix (respCell jStar F t)
        (respCoeffMinus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (respG F) hblk hb
  have hpath : ∀ a : CoeffSpace d,
      cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) (uM a))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
            (respxMinus P jStar F t e) := by
    intro a
    obtain ⟨lam, Lam, f, -, -, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus (F := F) hjStar hm t a
    have hmax : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f (aHarmonicFunctionOfAEEqCoeff hae (uM a)) :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (huM a)
    have hB3a : cellAverage (respCell jStar F t)
          (optimizerField f (aHarmonicFunctionOfAEEqCoeff hae (uM a)))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
            (respxMinus P jStar F t e) := by
      simpa only [respCell, respxMinus] using
        cellAverage_optimizerField_eq_blockResponseMean (respGrid jStar F) hgrid t hEll
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (aHarmonicFunctionOfAEEqCoeff hae (uM a)) hmax
    have hfield : optimizerField (respCoeffMinus F a) (uM a)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
          optimizerField f (aHarmonicFunctionOfAEEqCoeff hae (uM a)) := by
      filter_upwards [hae] with x hx
      simp only [optimizerField, grad_aHarmonicFunctionOfAEEqCoeff, hx]
    have hblock : blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
          (respxMinus P jStar F t e)
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
            (respxMinus P jStar F t e) :=
      congrArg (fun A => blockResponseMean A (respxMinus P jStar F t e))
        (coarseBlockMatrix_congr_of_ae_eq hae.symm)
    exact (cellAverage_congr_ae subset_rfl hfield).trans (hB3a.trans hblock)
  have hE : respYMinus P jStar F t e
      = blockResponseMean (annealedBlockOf P (respCell jStar F t) (respCoeffMinus F))
          (respxMinus P jStar F t e) := by
    rw [annealedBlockOf_respCoeffMinus_eq P jStar F t hquad hblk]
    rfl
  rw [hE, ← integral_blockResponseMean P (respCell jStar F t) (respCoeffMinus F)
    (respxMinus P jStar F t e) hA]
  refine Prod.ext ?_ ?_ <;> funext i <;> refine integral_congr_ae ?_ <;>
    filter_upwards [Filter.Eventually.of_forall hpath] with a ha <;> rw [ha]

/-- The adjoint twin of `respYMinus_eq_integral_cellAverage_optimizerField`: the annealed mean
`Y^+` of AK.HC (2.32) is the expectation of the cell average of the doubled optimizer state of
the terminal cell for the adjoint coefficient `a_+ = a^t + g`.  The pathwise identity is
applied to an almost everywhere elliptic representative of `a_+`, and the resulting statement is
transported back along the almost everywhere agreement of the optimizer fields and of the coarse
block matrices. -/
theorem respYPlus_eq_integral_cellAverage_optimizerField {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (hF : (toFullBlockMat F).PosDef)
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (huP : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) :
    respYPlus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P)) := by
  have hgrid : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (respCell jStar F t) (⇑a.1 : CoeffField d) := by
    intro a
    simpa only [respCell, adaptedCellTranslate_zero] using
      h7_hasQuadraticMu_adaptedCellTranslate (respGrid jStar F) hgrid t 0 a
  have hgskew : matTranspose (respg F) = -(respg F) := respCalib_respg_isSkew hF
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := h7_matTranspose_neg_skew hgskew
  have hbP : ∀ a : CoeffSpace d,
      coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)
        = blockCongr (ofFullBlockMat (toFullBlockMat (blockD d) *
            toFullBlockMat (⟨1, 0, -respg F, 1⟩ : BlockMat d)))
            (coarseBlock (respCell jStar F t) a) := by
    intro a
    have h1 : respCoeffPlus F a
        = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
      funext x
      simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
    have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := respCell jStar F t)
      (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
      (hasQuadraticMu_adjointCoeffField (hquad a))
    have h3 : coarseBlockMatrix (respCell jStar F t)
          (adjointCoeffField (⇑a.1 : CoeffField d))
        = blockCongr (blockD d) (coarseBlock (respCell jStar F t) a) := by
      rw [coarseBlockMatrix_adjointCoeffField_of_exists
        (exists_coarseBlockMatrix_of_hasQuadraticMu (hquad a)), ← blockCongr_blockD]
      rfl
    rw [h1, h2, h3, blockCongr_blockCongr]
  have hA : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix (respCell jStar F t)
        (respCoeffPlus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr _ hblk hbP
  have hpath : ∀ a : CoeffSpace d,
      cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) (uP a))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
            (respxPlus P jStar F t e) := by
    intro a
    obtain ⟨lam, Lam, f, -, -, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus (F := F) hjStar hm t a
    have hmax : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) f (aHarmonicFunctionOfAEEqCoeff hae (uP a)) :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (huP a)
    have hB3a : cellAverage (respCell jStar F t)
          (optimizerField f (aHarmonicFunctionOfAEEqCoeff hae (uP a)))
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
            (respxPlus P jStar F t e) := by
      simpa only [respCell, respxPlus] using
        cellAverage_optimizerField_eq_blockResponseMean (respGrid jStar F) hgrid t hEll
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (aHarmonicFunctionOfAEEqCoeff hae (uP a)) hmax
    have hfield : optimizerField (respCoeffPlus F a) (uP a)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
          optimizerField f (aHarmonicFunctionOfAEEqCoeff hae (uP a)) := by
      filter_upwards [hae] with x hx
      simp only [optimizerField, grad_aHarmonicFunctionOfAEEqCoeff, hx]
    have hblock : blockResponseMean (coarseBlockMatrix (respCell jStar F t) f)
          (respxPlus P jStar F t e)
        = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
            (respxPlus P jStar F t e) :=
      congrArg (fun A => blockResponseMean A (respxPlus P jStar F t e))
        (coarseBlockMatrix_congr_of_ae_eq hae.symm)
    exact (cellAverage_congr_ae subset_rfl hfield).trans (hB3a.trans hblock)
  have hE : respYPlus P jStar F t e
      = blockResponseMean (annealedBlockOf P (respCell jStar F t) (respCoeffPlus F))
          (respxPlus P jStar F t e) := by
    rw [annealedBlockOf_respCoeffPlus_eq P jStar F t hquad hblk]
    rfl
  rw [hE, ← integral_blockResponseMean P (respCell jStar F t) (respCoeffPlus F)
    (respxPlus P jStar F t e) hA]
  refine Prod.ext ?_ ?_ <;> funext i <;> refine integral_congr_ae ?_ <;>
    filter_upwards [Filter.Eventually.of_forall hpath] with a ha <;> rw [ha]

end

end Homogenization.HighContrast.Multiscale
