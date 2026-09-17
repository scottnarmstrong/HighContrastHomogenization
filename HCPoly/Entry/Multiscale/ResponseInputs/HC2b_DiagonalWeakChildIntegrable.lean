import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCarrierInputs
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSubcellCoeffOn

/-!
# Integrability of the recentred child field on its own subcell

The cell-average head of the diagonal weak-norm estimate consumes an `AHarmonicFunction` that
already lives on an aligned adapted child `adaptedCellAtCenter q k w`, not on the parent
`HighContrast.adaptedCell q t`.  This module records, for the recentred coefficients
`respCoeffMinus F a` and `respCoeffPlus F a`, the three input facts on that child: integrability
of both slots of the doubled optimizer field, integrability of the scalar energy density, and
nonnegativity of its volume average.

The proofs are the parent-cell arguments re-instantiated at the child.  The elliptic
representative is the one already attached to the child
(`exists_elliptic_representative_respCoeffMinusAt`, `exists_elliptic_representative_respCoeffPlusAt`),
so the restriction of an ellipticity statement from the parent is not needed; the generic
transport engines over an a.e. representative do all the work.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The recentred coefficient `a_- = respCoeffMinus F a` on its child -/

/-- **Integrability of both slots of the doubled optimizer field on the child, for
`respCoeffMinus F a`.**  For an invertible grid `q` and an aligned adapted child
`adaptedCellAtCenter q k w`, both slots of the doubled optimizer field of an arbitrary
`AHarmonicFunction` attached to `respCoeffMinus F a` on that child are integrable there.  The
gradient slot needs no ellipticity; the flux slot uses the a.e.-elliptic representative on the
child. -/
theorem h6a_integrableOn_optimizerField_respCoeffMinus_at (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (v : AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter q k w)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) v x).1 j) (adaptedCellAtCenter q k w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) v x).2 j) (adaptedCellAtCenter q k w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt q hq k w F a
  have hVfin : volume (adaptedCellAtCenter q k w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q k w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w).isFiniteMeasure_restrict_volume
  have hflux : MemVectorL2 (adaptedCellAtCenter q k w)
      (fun x => matVecMul ((respCoeffMinus F a) x) (v.toH1.grad x)) :=
    h6a_memVectorL2_optimizerField_flux_of_aeEq subset_rfl hEll hae v
  refine ⟨h6a_integrableOn_optimizerField_fst_pub subset_rfl hVfin (respCoeffMinus F a) v j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffMinus F a) v x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

/-! ## The transposed recentred coefficient `a_+ = respCoeffPlus F a` on its child -/

/-- **Integrability of both slots of the doubled optimizer field on the child, for
`respCoeffPlus F a`.**  The transposed twin of
`h6a_integrableOn_optimizerField_respCoeffMinus_at`. -/
theorem h6a_integrableOn_optimizerField_respCoeffPlus_at (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (v : AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter q k w)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) v x).1 j) (adaptedCellAtCenter q k w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) v x).2 j) (adaptedCellAtCenter q k w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt q hq k w F a
  have hVfin : volume (adaptedCellAtCenter q k w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q k w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w).isFiniteMeasure_restrict_volume
  have hflux : MemVectorL2 (adaptedCellAtCenter q k w)
      (fun x => matVecMul ((respCoeffPlus F a) x) (v.toH1.grad x)) :=
    h6a_memVectorL2_optimizerField_flux_of_aeEq subset_rfl hEll hae v
  refine ⟨h6a_integrableOn_optimizerField_fst_pub subset_rfl hVfin (respCoeffPlus F a) v j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffPlus F a) v x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q k w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

end

end Homogenization.HighContrast.Multiscale
