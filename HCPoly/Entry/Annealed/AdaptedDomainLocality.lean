import HCPoly.Entry.CG.Proofs.AdaptedDomainRecovery
import HCPoly.Entry.Geometry.AdaptedCell
import HCPoly.Entry.Geometry.StandardCell
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Provider.Recurrence.CellLocalMeasurability
import HCPoly.Setup.BlockAlgebra
import HCPoly.Setup.CoefficientSpace
import HCPoly.Setup.LocalSigmaFields
import HCPoly.Setup.Response
import Homogenization.CoarseGraining.BlockMatrixProperties
import Homogenization.CoarseGraining.CoarseBounds
import Homogenization.Geometry.Translation
import Mathlib.Probability.Independence.Basic

/-!
# The adapted cell's domain and its local σ-fields

Recovery of the adapted cell as a domain of the coarse block, and the local independence of the
coefficient field over separated cells that the annealed estimates are read in. On the actual
qualitative carrier, boundedness supplies a pointwise elliptic representative of each field on
the cell, giving strict positive definiteness of its coarse block and the mixed response formula;
the support-generated σ-fields of unit-separated cells are independent under a unit-range law.
The module serves the parent--child recurrence `p.fixed.geometry.parent.child.recurrence`.
-/

section
/-!
## Coefficient-carrier boundary for adapted-domain recovery support

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
end

section
/-!
## Local independence on the coefficient sigma-fields

This file works directly with the carrier `CoeffSpace` and the
support-generated sigma-fields `coeffSigma`.  It deliberately does not coerce
the law to an AKL fixed-ellipticity carrier.
-/

open Homogenization.HighContrast (CoeffSpace IsLocalTest UnitSeparated coeffPairing coeffSigma)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory ProbabilityTheory

noncomputable section

theorem coeffSigma_le_global
    {d : ℕ} (U : Set (Vec d)) :
    coeffSigma d U ≤ (inferInstance : MeasurableSpace (CoeffSpace d)) :=
  Recurrence.coeffSigma_mono (Set.subset_univ U)

theorem measurable_coeffPairing_local
    {d : ℕ} {U : Set (Vec d)} (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ : IsLocalTest U φ) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d U) inferInstance
      (coeffPairing e e' φ) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom ⟨e, e', φ, hφ, t, ht, rfl⟩

private theorem unitSeparated_biUnion_right {d : ℕ} {ι : Type*}
    {U : Set (Vec d)} {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, UnitSeparated U (V i)) :
    UnitSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact h i hi hx hyi

private theorem measurableSet_biInter_coeffSigma_biUnion {d : ℕ} {ι : Type*}
    {U : ι → Set (Vec d)}
    {f : ι → Set (CoeffSpace d)} {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (CoeffSpace d) (coeffSigma d (U i)) (f i)) :
    @MeasurableSet (CoeffSpace d)
      (coeffSigma d (⋃ i ∈ s, U i)) (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (CoeffSpace d)
            (coeffSigma d (⋃ j ∈ insert i s, U j)) (f i) :=
        (Recurrence.coeffSigma_mono hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (CoeffSpace d)
            (coeffSigma d (⋃ j ∈ insert i s, U j)) (⋂ j ∈ s, f j) :=
        (Recurrence.coeffSigma_mono hsubset_s)
          (⋂ j ∈ s, f j) (ih fun j hj => hf j (by simp [hj]))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

theorem iIndep_coeffSigma_of_isUnitRangeLaw
    {d : ℕ} {ι : Type*} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hP : IsUnitRangeLaw P) (U : ι → Set (Vec d))
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => UnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => coeffSigma d (U i)) P := by
  classical
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ => hU j
      have hsep_union : UnitSeparated (U i) (⋃ j ∈ s, U j) := by
        refine unitSeparated_biUnion_right (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (CoeffSpace d) (coeffSigma d (⋃ j ∈ s, U j))
            (⋂ j ∈ s, f j) :=
        measurableSet_biInter_coeffSigma_biUnion (U := U)
          (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := by
        exact (ProbabilityTheory.Indep_iff
          (coeffSigma d (U i)) (coeffSigma d (⋃ j ∈ s, U j)) P).1
            (hP (U i) (⋃ j ∈ s, U j) (hU i) hUnion hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        P (⋂ j ∈ insert i s, f j) = P (f i ∩ ⋂ j ∈ s, f j) := by simp
        _ = P (f i) * P (⋂ j ∈ s, f j) := h_inter
        _ = P (f i) * ∏ j ∈ s, P (f j) := by
          rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, P (f j) := by simp [Finset.prod_insert, hi]

theorem iIndepFun_of_coeffSigma_measurable
    {d : ℕ} {ι : Type*} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hP : IsUnitRangeLaw P) (U : ι → Set (Vec d))
    (hU : ∀ i, MeasurableSet (U i)) {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (X : ∀ i, CoeffSpace d → β i)
    (hX : ∀ i, @Measurable (CoeffSpace d) (β i) (coeffSigma d (U i))
      inferInstance (X i))
    (hsep : Pairwise fun i j => UnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndepFun X P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  exact (ProbabilityTheory.iIndep_iff (fun i => coeffSigma d (U i)) P).1
    (iIndep_coeffSigma_of_isUnitRangeLaw (P := P) hP U hU hsep) s
    (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

end

end Homogenization.HighContrast.Annealed
end
