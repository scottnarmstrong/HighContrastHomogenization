import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65a
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Setup.BlockAlgebra
import HCPoly.Entry.Geometry.AffineGridDistortion

/-!
# Law integrability of the recentred pathwise response

The recentring of the self-dual splitting sends the sample `a` to `a_- = a - g`, with `g` the
skew Schur coefficient of the canonical mean and `G = ((1, 0), (g, 1))` the constant shear.
Because `g` is constant and skew, the coarse block of `a_-` is the fixed congruence
`Gᵀ 𝐀(U; a) G` of the coarse block of `a`; the response `J(U; a_-)` is the corresponding block
quadratic minus the constant `p·q'`.  Consequently the law integrability of `J(U; a_-(·))`
follows from the entrywise law integrability of the recentred coarse block, which is itself a
fixed linear combination of the entries of `𝐀(U; ·)`.

This file records those two steps: the pathwise block identity (AK.HC (2.15) with the recentred
coefficient) and the reduction of the `P`-integrability of the response to the entrywise
`P`-integrability of the recentred coarse block.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock
  blockVecDot_blockMatVecMul_eq_sum coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The recentred coarse block is the shear congruence of the coarse block.  For the recentring
`a_- = a - g` of the self-dual splitting, the coarse block on an adapted cell is
`Gᵀ 𝐀(U_u; a) G` with the constant shear `G = ((1, 0), (g, 1))` whose off-diagonal block `g` is
the skew Schur coefficient of the canonical mean.  The proof uses only the skewness of `g` and
the quadraticity of the variational quantity on the cell. -/
theorem coarseBlockMatrix_respCoeffMinus_eq_blockCongr {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (u : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffMinus F a)
      = blockCongr (respG F) (coarseBlock (HighContrast.adaptedCell q u) a) := by
  exact coarseBlockMatrix_sub_skew_eq_blockCongr (U := HighContrast.adaptedCell q u)
    (a := (⇑a.1 : CoeffField d)) (g := respg F) (respg_isSkew F)
    (hasQuadraticMu_adaptedCell q hq u a)

/-- The recentred response is the block quadratic of its coarse block, AK.HC (2.15) for the
recentred coefficient `a_- = a - g`.  The two sides agree after passing to a pointwise
elliptic representative of `a_-` on the adapted cell and invoking the canonical
response--coarse-block identity on a bounded open convex domain. -/
theorem respJ_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (u : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    respJ q u p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffMinus F a))
            (-p, r))
        - vecDot p r := by
  obtain ⟨_, _, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq u F a
  have hdom : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q u) :=
    adaptedCell_isOpenBoundedConvexDomain q hq u
  have hvol : 0 < (volume (HighContrast.adaptedCell q u)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal q u]
    have hdet : 0 < |q.det| :=
      abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq))
    have hpow : 0 < ((3 : ℝ) ^ u) ^ d := by positivity
    exact mul_pos hdet hpow
  have hJ : ResponseJ (HighContrast.adaptedCell q u) p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffMinus F a))
            (-p, r))
        - vecDot p r := by
    rw [Homogenization.HighContrast.CG.responseJ_congr_of_ae_eq hae p r,
      Homogenization.coarseBlockMatrix_congr_of_ae_eq hae]
    exact Homogenization.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
      hdom hEll hvol p r
  exact hJ

/-- Law integrability of the recentred response from its pathwise block-quadratic form.  If
`b` is any coefficient family whose response is the block quadratic of its own coarse block, and
every entry of that coarse block is `P`-integrable, then the response is `P`-integrable.  The
quadratic form is expanded in the canonical block basis, so it is a finite real combination of
the entries of the coarse block, and the constant `p·q'` is integrable because `P` is a finite
measure. -/
theorem integrable_respJ_of_pathwise {d : ℕ} (P : MeasureTheory.Measure (CoeffSpace d))
    [MeasureTheory.IsFiniteMeasure P] (qq : Mat d) (u : ℤ) (p q' : Vec d)
    (b : CoeffSpace d → CoeffField d)
    (hpath : ∀ a : CoeffSpace d, respJ qq u p q' (b a)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) (-p, q'))
        - vecDot p q')
    (hint : ∀ α β : BlockCoord d, MeasureTheory.Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) α β) P) :
    MeasureTheory.Integrable (fun a => respJ qq u p q' (b a)) P := by
  have hQ : MeasureTheory.Integrable (fun a => blockVecDot (-p, q')
      (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) (-p, q'))) P := by
    have heq : (fun a => blockVecDot (-p, q')
        (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) (-p, q')))
        = fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec (-p, q') α *
              (blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) α β *
                toFullBlockVec (-p, q') β) := by
      funext a
      rw [blockVecDot_blockMatVecMul_eq_sum]
    rw [heq]
    refine integrable_finsetSum Finset.univ (fun α _ => ?_)
    refine integrable_finsetSum Finset.univ (fun β _ => ?_)
    exact ((hint α β).mul_const (toFullBlockVec (-p, q') β)).const_mul
      (toFullBlockVec (-p, q') α)
  have hmain : MeasureTheory.Integrable (fun a => (1 / 2 : ℝ) * blockVecDot (-p, q')
        (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) (-p, q'))
      - vecDot p q') P :=
    (hQ.const_mul (1 / 2 : ℝ)).sub (integrable_const (vecDot p q'))
  exact hmain.congr (Filter.Eventually.of_forall fun a => (hpath a).symm)

/-- Law integrability of the recentred response for the response coefficient `a_- = a - g`:
the pathwise representation `respJ_respCoeffMinus_eq` together with the transport of the
entrywise integrability of the coarse block across the constant shear congruence yields
`P`-integrability of `a ↦ J(U_u; a_-(a))`. -/
theorem integrable_respJ_respCoeffMinus {d : ℕ} [NeZero d]
    (P : MeasureTheory.Measure (CoeffSpace d)) [MeasureTheory.IsFiniteMeasure P]
    (jStar : ℕ) (F : BlockMat d) (u : ℤ) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) (p q' : Vec d) :
    MeasureTheory.Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffMinus F a)) P := by
  refine integrable_respJ_of_pathwise P (respGrid jStar F) u p q' (respCoeffMinus F) ?_ ?_
  · intro a
    exact respJ_respCoeffMinus_eq (respGrid jStar F) hq u F a p q'
  · simpa only [respCell] using
      integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
        (V := respCell jStar F u) (b := respCoeffMinus F) hint
        (fun a => coarseBlockMatrix_respCoeffMinus_eq_blockCongr (respGrid jStar F) hq u F a)

end

end Homogenization.HighContrast.Multiscale
