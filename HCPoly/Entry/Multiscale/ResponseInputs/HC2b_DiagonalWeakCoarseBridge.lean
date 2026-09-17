import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentResponseField

/-!
# The Chapter-2 coarse block of an adapted cell is the shear congruence

This module discharges the identification that the recent-difference and parent energy maps carry
as an explicit hypothesis: the Chapter-2 coarse block matrix of the recentred coefficient on an
aligned adapted cell is the shear congruence of the cell's set-level coarse block.

The two coarse-block carriers are not syntactically the same object.  Chapter 2 builds the block
from the doubled variational quantity `𝐀(U; a)` through the `sigma`/`kappa` recovery package,
while the set-level block is assembled directly from `Mu` by polarization.  The two constructions
agree on every Chapter-2 domain: Chapter-2's `doubledMu` is the set-level `Mu` of the coefficient
field (`book_doubledMu_eq_Mu`), and a block is determined by its `Mu` quadratic form
(`IsCoarseBlockMatrix` and `eq_coarseBlockMatrix_of_isCoarseBlockMatrix`).  That is the content of
`h6a_coarseBlockMatrix_domain_eq_set`.

The shear congruence itself is the set-level identity for a field recentred by a skew matrix: the
quadratic form of `a x - g` is the quadratic form of `a` at the sheared state
`(p, g p + q)`, so the recentred block is `Gᵀ 𝐀 G`.  This is `h6a_hcoarse_minus`; the adjoint twin
`h6a_hcoarse_plus` composes it with the flux sign flip `D = diag(Id, -Id)`.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace Mu_congr_ae adaptedCellCenter coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- **The Chapter-2 coarse block of a `Domain` is the set-level coarse block of its
representative.**  Chapter-2's `doubledMu` is the set-level `Mu` of the coefficient field, and a
symmetric block is determined by its `Mu` quadratic form, so the two constructions coincide. -/
theorem h6a_coarseBlockMatrix_domain_eq_set {U : Book.Ch02.Domain d}
    (aU : Book.Ch02.CoeffOn U) :
    Book.Ch02.coarseBlockMatrix U aU = coarseBlockMatrix (U : Set (Vec d)) aU.toCoeffField := by
  refine eq_coarseBlockMatrix_of_isCoarseBlockMatrix ⟨?_, ?_⟩
  · exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U aU
  · intro P
    exact (Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U aU P).symm.trans
      ((Book.Ch02.doubledMuTheory U aU).doubledMu_eq_coarseBlockMatrix P)

/-- **The coarse block of a field on an aligned adapted cell satisfies the variational
characterization.**  A pointwise elliptic representative exists on the cell; CG's convex-domain
recovery supplies the `Mu` quadratic form for that representative, and `Mu` is insensitive to
changing the field on a null set. -/
theorem h6a_isCoarseBlockMatrix_adaptedCellAtCenter [NeZero d] (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    IsCoarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)
      (coarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q k w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w
  have hvol : 0 < (volume (adaptedCellAtCenter q k w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos q hq k w
  have hA : IsCoarseBlockMatrix (adaptedCellAtCenter q k w) f
      (coarseBlockMatrix (adaptedCellAtCenter q k w) f) :=
    isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hConv hEll hvol
  refine ⟨isSymmetricBlockMat_coarseBlockMatrix _ _, ?_⟩
  intro P
  rw [Mu_congr_ae hae P, hA.2 P,
    coarseBlockMatrix_congr_of_ae_eq (U := adaptedCellAtCenter q k w) (ae_restrict_of_ae hae)]

/-- **The set-level shear identity from the variational characterization.**  If the set-level
coarse block of `a` is characterized by `Mu`, then recentring by a skew matrix `g` turns the
recentred block into the congruence of the block by `G = ((1, 0), (g, 1))`.  This is the
`IsCoarseBlockMatrix` form of the shear step, which avoids a separate quadraticity hypothesis. -/
theorem h6a_coarseBlockMatrix_sub_skew_of_isCoarse {U : Set (Vec d)} {a : CoeffField d}
    {g : Mat d} {A : BlockMat d} (hg : matTranspose g = -g) (hA : IsCoarseBlockMatrix U a A) :
    coarseBlockMatrix U (fun x => a x - g) = blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A := by
  have hnew : IsCoarseBlockMatrix U (fun x => a x - g)
      (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) := by
    refine ⟨isSymmetricBlockMat_blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) hA.1, ?_⟩
    intro P
    rw [Mu_sub_skew hg U P a, hA.2 (blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P),
      blockVecDot_blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A P]
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hnew).symm

/-- **The recentred coarse block of an aligned cell is the shear congruence of the cell's coarse
block, minus sign.**  This is the identity the recent-difference energy map consumes: the
Chapter-2 block of the recentred coefficient equals `Gᵀ 𝐀 G` for the cell's set-level coarse
block. -/
theorem h6a_hcoarse_minus [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (aU : Book.Ch02.CoeffOn (adaptedDomainAt q hq k w))
    (haU : aU.toCoeffField = respCoeffMinus F a) :
    Book.Ch02.coarseBlockMatrix (adaptedDomainAt q hq k w) aU
      = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q k w) a) := by
  rw [h6a_coarseBlockMatrix_domain_eq_set aU, adaptedDomainAt_carrier, haU]
  exact h6a_coarseBlockMatrix_sub_skew_of_isCoarse (respg_isSkew F)
    (h6a_isCoarseBlockMatrix_adaptedCellAtCenter q hq k w a)

/-- **The recentred coarse block of an aligned cell is the composed congruence of the cell's
coarse block, plus sign.**  The recentred adjoint field is `respCoeffPlus F a = aᵀ + g`, so the
shear identity applies at the adjoint field with skew `-g`, and the adjoint block is the flux
sign flip `D` of the primal block.  This matches the `hcoarse` shape of the adjoint energy map. -/
theorem h6a_hcoarse_plus [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (aU : Book.Ch02.CoeffOn (adaptedDomainAt q hq k w))
    (haU : aU.toCoeffField = respCoeffPlus F a) :
    Book.Ch02.coarseBlockMatrix (adaptedDomainAt q hq k w) aU
      = blockCongr (blockD d)
          (blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q k w) a)) := by
  rw [h6a_coarseBlockMatrix_domain_eq_set aU, adaptedDomainAt_carrier, haU]
  have hA_a : IsCoarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)
      (coarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d)) :=
    h6a_isCoarseBlockMatrix_adaptedCellAtCenter q hq k w a
  have hex : ∃ A : BlockMat d,
      IsCoarseBlockMatrix (adaptedCellAtCenter q k w) (⇑a.1 : CoeffField d) A :=
    ⟨_, hA_a⟩
  have hA_b : IsCoarseBlockMatrix (adaptedCellAtCenter q k w)
      (adjointCoeffField (⇑a.1 : CoeffField d))
      (coarseBlockMatrix (adaptedCellAtCenter q k w) (adjointCoeffField (⇑a.1 : CoeffField d))) := by
    have h := IsCoarseBlockMatrix.adjointCoeffField_symm hA_a
    rw [← blockCongr_blockD] at h
    rw [coarseBlockMatrix_adjointCoeffField_of_exists hex, ← blockCongr_blockD]
    exact h
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    show (-(respg F) : Mat d)ᵀ = -(-(respg F))
    rw [Matrix.transpose_neg]
    exact congrArg Neg.neg (respg_isSkew F)
  have hplus : respCoeffPlus F a
      = fun x => adjointCoeffField (⇑a.1 : CoeffField d) x - (-(respg F)) := by
    funext x
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  rw [hplus, h6a_coarseBlockMatrix_sub_skew_of_isCoarse (U := adaptedCellAtCenter q k w)
      (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew hA_b,
    coarseBlockMatrix_adjointCoeffField_of_exists hex, ← blockCongr_blockD,
    blockCongr_blockCongr, blockD_mul_shear_neg, ← blockCongr_blockCongr]
  rfl

end

end Homogenization.HighContrast.Multiscale
