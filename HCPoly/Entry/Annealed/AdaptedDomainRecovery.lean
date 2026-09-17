import HCPoly.Entry.CG.Proofs.AdaptedDomainRecovery
import HCPoly.Entry.Geometry.AdaptedCell
import HCPoly.Entry.Setup.Response

/-!
# Coefficient-carrier boundary for adapted-domain recovery support

This file transports strict positivity and the mixed response formula from CG affine open
cubes to the qualitative coefficient carrier. Boundedness supplies each field's
ellipticity constants on the cell; a.e. congruence returns both observables to its original
representative. The endpoints assume no law-integrability or law-uniform ellipticity bound.

Source: near `e.scale.selection.normalized.mean.fluctuation`, `p.fixed.geometry.parent.child.recurrence`; the pathwise block structure
comes from HC. Annealed positivity still requires the
separate law-integrability input to the existing expectation theorem.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace coarseBlock coarseBlock_eq_of_ae_eq
  exists_pointwise_elliptic_representative)

namespace Homogenization.HighContrast.Annealed

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem adaptedCellTranslate_eq_cg_affine
    {d : ℕ} (q : Mat d) (j : ℤ) (y : Vec d) :
    HighContrast.adaptedCellTranslate q j y =
      translateSet y (matVecMul q '' openCubeSet (originCube d j)) := by
  ext x
  constructor
  · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨matVecMul q v, ⟨v, hv, rfl⟩, by ext i; simp [add_comm]⟩
  · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨matVecMul q v, ⟨v, hv, rfl⟩, by ext i; simp [add_comm]⟩

/-- Boundedness supplies a pointwise elliptic representative of each qualitative field on the
cell. The constants depend only on this field and region and remain internal to the pathwise
proof. -/
theorem exists_elliptic_representative_adapted
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCellTranslate q j y) f ∧
        (⇑a.1 : CoeffField d) =ᵐ[volume] f := by
  classical
  have hdomain : IsOpenBoundedConvexDomain (HighContrast.adaptedCellTranslate q j y) := by
    rw [adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq j y
  obtain ⟨lam, Lam, f, hlam, hle, hfm, hfp, hfa⟩ :=
    exists_pointwise_elliptic_representative a.2 hdomain.isBoundedDomain.isBounded
  refine ⟨lam, Lam, f, hlam, hle, ⟨?_, hfp⟩, hfa⟩
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun k =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hfm)).ite
      hdomain.isOpen.measurableSet measurable_const

/-- Pathwise strict positivity on the actual qualitative coefficient carrier. -/
theorem blockPosDef_coarseBlock_adapted
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (coarseBlock (HighContrast.adaptedCellTranslate q j y) a) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_adapted q hq j y a
  rw [coarseBlock_eq_of_ae_eq a hae, adaptedCellTranslate_eq_cg_affine]
  rw [adaptedCellTranslate_eq_cg_affine] at hEll
  exact blockPosDef_coarseBlockMatrix_affine_openCube q hq j y f hEll

/-- The mixed response formula for the coefficient representative and coarse block. -/
theorem responseJ_eq_coarseBlock_adapted
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ (HighContrast.adaptedCellTranslate q j y) p r (⇑a.1) =
      (1 / 2 : ℝ) * blockVecDot (-p, r)
        (blockMatVecMul (coarseBlock (HighContrast.adaptedCellTranslate q j y) a) (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_adapted q hq j y a
  rw [responseJ_congr_of_ae_eq (ae_restrict_of_ae hae), coarseBlock_eq_of_ae_eq a hae,
    adaptedCellTranslate_eq_cg_affine]
  rw [adaptedCellTranslate_eq_cg_affine] at hEll
  exact responseJ_eq_block_quadratic_affine_openCube q hq j y f hEll p r

end Homogenization.HighContrast.Annealed
