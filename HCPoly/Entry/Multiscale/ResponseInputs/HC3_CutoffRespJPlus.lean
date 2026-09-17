import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65a
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Setup.BlockAlgebra
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRespJIntegrable

/-!
# Law integrability of the adjoint recentred pathwise response

The pathwise response `J(U, p, q; b)` of a sample coefficient is a supremum, and on an adapted
cell it agrees with the quadratic expression `½ x · 𝐀(U; b) x - p · q` of the coarse block
whenever `b` is elliptic.  This file records that agreement for the adjoint recentred
coefficient `a₊ = aᵗ + g`, where `g` is the skew Schur half of the self-dual splitting, and
deduces that the annealed response `a ↦ J(U, p, q; a₊)` is integrable for the law as soon as
the entries of the coarse block `𝐀(U; a)` are.

The two structural facts are:

* the adjoint of a coefficient reflects its coarse block in the flux slot, and recentring by
  the skew half `g` is the constant shear congruence `G` of the self-dual splitting, so
  `𝐀(U; a₊) = (G·D)ᵀ 𝐀(U; a) (G·D)`;
* the doubled quadratic form of a constant congruence is a finite linear combination of the
  entries of `𝐀(U; a)`, hence inherits their integrability.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Coarse block of the adjoint recentred coefficient.**  For every sample `a` the coarse
block of the adjoint recentred coefficient `a₊ = aᵗ + g` is the constant congruence, by the
shear `G` of the self-dual splitting and the flux reflection `D = diag(Id, -Id)`, of the coarse
block of `a`.  The adjoint transpose reflects the coarse block in the flux slot and the
recentring by the skew Schur half `g` shears it. -/
theorem coarseBlockMatrix_respCoeffPlus_eq_blockCongr {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (u : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a)
      = blockCongr (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
          (coarseBlock (HighContrast.adaptedCell q u) a) := by
  have hgskew : matTranspose (respg F) = -(respg F) := respg_isSkew F
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    ext i j
    have h := congrFun (congrFun hgskew i) j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at h ⊢
    linarith [h]
  have hquad := hasQuadraticMu_adaptedCell q hq u a
  have h1 : respCoeffPlus F a
      = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
    funext x
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := HighContrast.adaptedCell q u)
    (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
    (hasQuadraticMu_adjointCoeffField hquad)
  have h3 : coarseBlockMatrix (HighContrast.adaptedCell q u)
        (adjointCoeffField (⇑a.1 : CoeffField d))
      = blockCongr (blockD d) (coarseBlock (HighContrast.adaptedCell q u) a) := by
    rw [coarseBlockMatrix_adjointCoeffField_of_exists
      (exists_coarseBlockMatrix_of_hasQuadraticMu hquad), ← blockCongr_blockD]
    rfl
  rw [h1, h2, h3, blockCongr_blockCongr, blockD_mul_shear_neg (respg F)]
  rfl

/-- **The pathwise response of the adjoint recentred coefficient.**  On the adapted cell the
pathwise response of `a₊ = aᵗ + g` is the quadratic expression of the coarse block: the
coefficient is almost everywhere equal to a uniformly elliptic representative, and the response
and the coarse block depend only on the almost everywhere class. -/
theorem respJ_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (u : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    respJ q u p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a))
            (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, -, -, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq u F a
  have hConv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q u) :=
    adaptedCell_isOpenBoundedConvexDomain q hq u
  have hvol : 0 < (volume (HighContrast.adaptedCell q u)).toReal :=
    ENNReal.toReal_pos (hConv.isOpen.measure_ne_zero volume (adaptedCell_nonempty q u))
      hConv.volume_lt_top.ne
  have hJ : respJ q u p r (respCoeffPlus F a) = respJ q u p r f := by
    unfold respJ
    exact responseJ_congr_of_ae_eq hae p r
  have hblock : coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q u) f :=
    coarseBlockMatrix_congr_of_ae_eq hae
  rw [hJ]
  unfold respJ
  rw [responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hConv hEll hvol p r, hblock]

/-- **Law integrability of the adjoint recentred pathwise response.**  For the adjoint recentred
coefficient `a₊ = aᵗ + g` of a sample `a`, the pathwise response of the adapted cell is
integrable for the law as soon as the entries of the coarse block `𝐀(U; a)` are: the recentring
is a constant congruence of that coarse block, and the quadratic form of a constant congruence
is a finite combination of its entries. -/
theorem integrable_respJ_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsFiniteMeasure P]
    (jStar : ℕ) (F : BlockMat d) (u : ℤ) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) (p q' : Vec d) :
    MeasureTheory.Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffPlus F a)) P := by
  refine integrable_respJ_of_pathwise P (respGrid jStar F) u p q' (respCoeffPlus F)
    (fun a => respJ_respCoeffPlus_eq (respGrid jStar F) hq u F a p q') ?_
  exact integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr
    (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
    hint (fun a => coarseBlockMatrix_respCoeffPlus_eq_blockCongr (respGrid jStar F) hq u F a)

end

end Homogenization.HighContrast.Multiscale
